/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import Mathlib.Algebra.IsPrimePow

namespace MetaMathlibExt

@[expose] public section

/-- **Gaussian partition.** A Gaussian partition is represented by its list of subspace
dimensions, which is a nonincreasing list of natural numbers. -/
structure GaussianPartition where
  dims : List ℕ
  sorted_desc : List.Pairwise (· ≥ ·) dims

/-- **Block.** A block is a pair $(d, m)$ of natural numbers, read as a part size $d$ of an integer
partition together with its multiplicity $m$. No condition is imposed on a single block. -/
structure Block where
  d : Nat
  m : Nat
deriving DecidableEq, Repr

/-- **Branch step.** A branch step is a triple $(a, b, c)$ of natural numbers. It describes one
simultaneous split level: for the ambient parameter $q$, $c$ copies of the parent dimension
$a + b$ become $c$ copies of $a$ and $c q^a$ copies of $b$. -/
structure BranchStep where
  a : Nat
  b : Nat
  c : Nat
deriving DecidableEq, Repr

def blockWeight (B : Block) : Nat := B.m * B.d

def prefixAt (blocks : List Block) (i : Nat) : Nat :=
  ((blocks.take i).map blockWeight).sum

def blockAt (blocks : List Block) (i : Nat) : Block :=
  blocks[i]?.getD ⟨0, 0⟩

/-- **Basic block multiplicity.** Let $q$ be a natural number and
$(d_0, m_0), \dots, (d_{k-1}, m_{k-1})$ a list of blocks, and put $p_i = \sum_{j < i} m_j d_j$.
The basic multiplicity of block $i$ is $N_i = \sum_{j=0}^{m_i - 1} q^{p_i + j d_i}$ when $i < k$,
and $N_i = 0$ when $i \ge k$. -/
def basicCount (q : Nat) (blocks : List Block) (i : Nat) : Nat :=
  match blocks[i]? with
  | none => 0
  | some B => ((List.range B.m).map (fun j => q ^ (prefixAt blocks i + j * B.d))).sum

/-- **First-split exponent.** Let $(d_0, m_0), \dots, (d_{k-1}, m_{k-1})$ be a list of blocks and
put $p_i = \sum_{j < i} m_j d_j$. The first-split exponent of block $i$ is
$u_i = p_i + (m_i - 1) d_i$ when $i < k$, where $m_i - 1$ is taken to be $0$ if $m_i = 0$, and
$u_i = 0$ when $i \ge k$. -/
def branchBoundExp (blocks : List Block) (i : Nat) : Nat :=
  match blocks[i]? with
  | none => 0
  | some B => prefixAt blocks i + (B.m - 1) * B.d

def blockBasicDims (q : Nat) (blocks : List Block) (i : Nat) : List Nat :=
  match blocks[i]? with
  | none => []
  | some B => List.replicate (basicCount q blocks i) B.d

def basicSegs (q : Nat) (blocks : List Block) : List (List Nat) :=
  (List.range blocks.length).map (blockBasicDims q blocks)

def basicGlobalDims (q : Nat) (blocks : List Block) : List Nat :=
  (basicSegs q blocks).flatten

def chainAt (chains : List (List BranchStep)) (i : Nat) : List BranchStep :=
  match chains[i]? with
  | none => []
  | some ch => ch

/-- **Removing the first occurrences of an entry.** Let $x$ and $c$ be natural numbers and let
$l$ be a list of natural numbers. For $c = 0$ the result is the pair of the empty list and $l$.
For $c \ge 1$, if $l$ has at least $c$ entries equal to $x$, the result is the pair of the list
of entries different from $x$ that come before the $c$-th entry equal to $x$, in their order in
$l$, and the part of $l$ after that entry. If $l$ has fewer than $c$ entries equal to $x$, there
is no result. -/
def removeFirstNPos (x c : Nat) : List Nat → Option (List Nat × List Nat)
  | [] => if c = 0 then some ([], []) else none
  | y :: ys =>
    match c with
    | 0 => some ([], y :: ys)
    | n + 1 =>
      if y = x then removeFirstNPos x n ys
      else (removeFirstNPos x (n + 1) ys).map (fun p => (y :: p.1, p.2))

/-- **Split replacement in a dimension list.** For natural numbers $q, a, b, c$ and a list $l$ of
natural numbers, the split replacement is defined exactly when $l$ has at least $c$ entries equal
to $a + b$. It removes the last $c$ entries of $l$ equal to $a + b$ and, at the position of the
first of these removed entries, inserts $c$ copies of $a$ followed by $c q^a$ copies of $b$; the
entries of $l$ before that position stay in front, and the entries after it that were not removed
follow in their original order. For $c = 0$ the list is unchanged.

No sorting is performed. -/
def applySplit (q a b c : Nat) (l : List Nat) : Option (List Nat) :=
  match removeFirstNPos (a + b) c l.reverse with
  | none => none
  | some (beforeRev, restRev) =>
    some (restRev.reverse ++ List.replicate c a ++
      List.replicate (c * q ^ a) b ++ beforeRev.reverse)

def applyChain (q : Nat) (l : List Nat) : List BranchStep → Option (List Nat)
  | [] => some l
  | s :: rest =>
    match applySplit q s.a s.b s.c l with
    | none => none
    | some l' => applyChain q l' rest

/-- **Final dimensions of a block.** Let $q$ be a natural number,
$(d_0, m_0), \dots, (d_{k-1}, m_{k-1})$ a list of blocks and $C$ a list of chains of branch steps.
The final dimension list of block $i$ is defined when $C$ has an entry $s_1, \dots, s_r$ at index
$i$: start from $N_i$ copies of $d_i$, where $N_i$ is the basic multiplicity of block $i$ (the
empty list when $i \ge k$), and for $t = 1, \dots, r$ in order apply the split replacement of step
$s_t = (a_t, b_t, c_t)$, which replaces $c_t$ copies of $a_t + b_t$ by $c_t$ copies of $a_t$ and
$c_t q^{a_t}$ copies of $b_t$. It is undefined when $C$ has no entry at index $i$ or when one of
these split replacements is undefined. -/
def blockFinalDims (q : Nat) (blocks : List Block)
    (chains : List (List BranchStep)) (i : Nat) : Option (List Nat) :=
  match chains[i]? with
  | none => none
  | some ch => applyChain q (blockBasicDims q blocks i) ch

def allFinalDimsAux (q : Nat) (blocks : List Block)
    (chains : List (List BranchStep)) : Nat → Option (List (List Nat))
  | 0 => some []
  | t + 1 =>
    match allFinalDimsAux q blocks chains t with
    | none => none
    | some acc =>
      match blockFinalDims q blocks chains t with
      | none => none
      | some cur => some (acc ++ [cur])

def allFinalDims (q : Nat) (blocks : List Block)
    (chains : List (List BranchStep)) : Option (List (List Nat)) :=
  allFinalDimsAux q blocks chains blocks.length

def sequenceOptSeg : List (Option (List Nat)) → Option (List (List Nat))
  | [] => some []
  | none :: _ => none
  | some x :: xs => (sequenceOptSeg xs).map (x :: ·)

/-- **Stage segments of a restricted Gaussian partition.** Let $q$ be a natural number, let
$(d_0, m_0), \dots, (d_{\ell-1}, m_{\ell-1})$ be blocks, let $C_0, C_1, \dots$ be chains of
branch steps, let $F_0, F_1, \dots$ be lists of natural numbers, and let $i$ and $k$ be natural
numbers; blocks, chains and lists are indexed from $0$. With $p_h = \sum_{g < h} m_g d_g$, the
basic segment of block $h$ is the list of $\sum_{j=0}^{m_h - 1} q^{p_h + j d_h}$ copies of $d_h$.
A step $(a, b, c)$ acts on a list by deleting its last $c$ entries equal to $a + b$ and putting
$c$ copies of $a$ followed by $c q^a$ copies of $b$ where the first deleted entry was, after the
entries before it and before the remaining entries after it (a step with $c = 0$ changes
nothing); it fails if the list has fewer than $c$ entries equal to $a + b$.

The stage segments at $(i, k)$ form the list of $\ell$ segments whose entry for block $h$ is
$F_h$ if $h < i$; the result of applying the first $k + 1$ steps of $C_i$ in order to the basic
segment of block $i$ if $h = i$ (all steps of $C_i$ if it has at most $k + 1$, and none if there
is no chain $C_i$); and the basic segment of block $h$ if $h > i$. They are undefined if $F_h$ is
missing for some block $h < i$ or one of these steps fails. -/
def stageSegments (q : Nat) (blocks : List Block) (chains : List (List BranchStep))
    (finals : List (List Nat)) (i k : Nat) : Option (List (List Nat)) :=
  sequenceOptSeg ((List.range blocks.length).map fun h =>
    if h < i then finals[h]?
    else if h = i then
      applyChain q (blockBasicDims q blocks h) ((chainAt chains h).take (k + 1))
    else some (blockBasicDims q blocks h))

def stageGlobalDims (q : Nat) (blocks : List Block) (chains : List (List BranchStep))
    (finals : List (List Nat)) (i k : Nat) : Option (List Nat) :=
  (stageSegments q blocks chains finals i k).map List.flatten

def BlocksStructValid (blocks : List Block) (n : Nat) : Prop :=
  (∀ B ∈ blocks, 1 ≤ B.d) ∧
  (∀ B ∈ blocks, 1 ≤ B.m) ∧
  (∀ p ∈ blocks.zip blocks.tail, p.1.d > p.2.d) ∧
  (blocks.map blockWeight).sum = n

instance decBlocksStructValid (blocks : List Block) (n : Nat) :
    Decidable (BlocksStructValid blocks n) := by
  unfold BlocksStructValid
  exact inferInstance

def ChainHeadValid (q : Nat) (blocks : List Block) (i : Nat) (s : BranchStep) : Prop :=
  1 ≤ s.b ∧ s.b ≤ s.a ∧ s.a + s.b = (blockAt blocks i).d ∧ 1 ≤ s.c ∧
    s.c ≤ q ^ branchBoundExp blocks i - 1 ∧ basicCount q blocks i ≠ 1

instance decChainHeadValid (q : Nat) (blocks : List Block) (i : Nat)
    (s : BranchStep) : Decidable (ChainHeadValid q blocks i s) := by
  unfold ChainHeadValid
  exact inferInstance

/-- **Adjacently valid chain.** A chain of branch steps
$(a_1, b_1, c_1), \dots, (a_r, b_r, c_r)$ is adjacently valid when for every $j$ with
$1 \le j < r$ we have $a_{j+1} + b_{j+1} = a_j$, $1 \le b_{j+1} \le a_{j+1}$ and
$1 \le c_{j+1} \le c_j$. Only consecutive steps are related, and nothing is required of the first
step alone; in particular every chain with at most one step is adjacently valid. -/
def ChainAdjValid (ch : List BranchStep) : Prop :=
  ((ch.zip ch.tail).all (fun p =>
    decide (p.2.a + p.2.b = p.1.a ∧ 1 ≤ p.2.b ∧ p.2.b ≤ p.2.a ∧
      1 ≤ p.2.c ∧ p.2.c ≤ p.1.c)) = true)

instance decChainAdjValid (ch : List BranchStep) :
    Decidable (ChainAdjValid ch) := by
  unfold ChainAdjValid
  exact inferInstance

/-- **Valid branch.** Let $q$ be a natural number, $(d_0, m_0), \dots, (d_{k-1}, m_{k-1})$ a list
of blocks and $i$ an index, and let $u_i$ and $N_i$ be the first-split exponent and the basic
multiplicity of block $i$, with $d_i$ read as $0$ when $i \ge k$. A chain of branch steps
$(a_1, b_1, c_1), \dots, (a_r, b_r, c_r)$ is a valid branch for block $i$ when either $r = 0$, or
$r \ge 1$, the first step satisfies $1 \le b_1 \le a_1$, $a_1 + b_1 = d_i$ and
$1 \le c_1 \le q^{u_i} - 1$ (subtraction truncated at $0$), $N_i \ne 1$, and the chain is
adjacently valid. -/
def BranchValid (q : Nat) (blocks : List Block) (i : Nat)
    (ch : List BranchStep) : Prop :=
  match ch with
  | [] => True
  | s :: _ => ChainHeadValid q blocks i s ∧ ChainAdjValid ch

instance decBranchValid (q : Nat) (blocks : List Block) (i : Nat)
    (ch : List BranchStep) : Decidable (BranchValid q blocks i ch) := by
  cases ch with
  | nil => exact isTrue True.intro
  | cons s rest =>
    exact inferInstanceAs
      (Decidable (ChainHeadValid q blocks i s ∧ ChainAdjValid (s :: rest)))

/-- **Restricted Gaussian partition.** Let $q$ and $n$ be natural numbers and let $G$ be a
Gaussian partition. Then $G$ is a restricted Gaussian partition for $q$ and $n$ when $q$ is a
prime power, $n > 0$, and there exist blocks $(d_1, m_1), \dots, (d_\ell, m_\ell)$ and, for each
block $i$, a chain $C_i$ of branch steps $(a, b, c)$, with the following properties.

The blocks satisfy $d_i \ge 1$ and $m_i \ge 1$ for every $i$, $d_1 > d_2 > \dots > d_\ell$ and
$m_1 d_1 + \dots + m_\ell d_\ell = n$. With $p_i = \sum_{h < i} m_h d_h$, the basic segment of
block $i$ is the list of $\beta_i = \sum_{j=0}^{m_i - 1} q^{p_i + j d_i}$ copies of $d_i$.

Each chain $C_i$ is empty or satisfies the following: its first step $(a, b, c)$ has
$1 \le b \le a$, $a + b = d_i$, $1 \le c \le q^{p_i + (m_i - 1) d_i} - 1$ and $\beta_i \ne 1$,
and each pair of consecutive steps $(a, b, c), (a', b', c')$ has $a' + b' = a$,
$1 \le b' \le a'$ and $1 \le c' \le c$.

A step $(a, b, c)$ acts on a list of dimensions by deleting its last $c$ entries equal to
$a + b$ and putting $c$ copies of $a$ followed by $c q^a$ copies of $b$ where the first deleted
entry was, after the entries before it and before the remaining entries after it; it fails if
the list has fewer than $c$ entries equal to $a + b$. Applying the steps of $C_i$ in order to the
basic segment of block $i$ succeeds for every $i$, with final segment $F_i$.

The concatenation of the basic segments is nonincreasing, the concatenation $F_1 \cdots F_\ell$
is nonincreasing, and for every block $i$ and every $k$ smaller than the length of $C_i$, the
concatenation of $F_1, \dots, F_{i-1}$, the result of applying the first $k + 1$ steps of $C_i$
to the basic segment of block $i$, and the basic segments of blocks $i + 1, \dots, \ell$ is
nonincreasing. Finally, the dimension list of $G$ is $F_1 \cdots F_\ell$. -/
def IsRestrictedGaussianPartition (q n : Nat) (G : GaussianPartition) : Prop :=
  IsPrimePow q ∧ 0 < n ∧
    ∃ (blocks : List Block) (chains : List (List BranchStep)),
      chains.length = blocks.length ∧
      BlocksStructValid blocks n ∧
      (∀ i, i < blocks.length → BranchValid q blocks i (chainAt chains i)) ∧
      ∃ (finals : List (List Nat)),
        allFinalDims q blocks chains = some finals ∧
        (basicGlobalDims q blocks).Pairwise (fun a b : Nat => a ≥ b) ∧
        finals.flatten.Pairwise (fun a b : Nat => a ≥ b) ∧
        (∀ i, i < blocks.length →
          ∀ k, k < (chainAt chains i).length →
            (stageGlobalDims q blocks chains finals i k).all
              (fun g => decide (g.Pairwise (fun a b : Nat => a ≥ b))) = true) ∧
        G.dims = finals.flatten

/-- **Basic ancestors are restricted.** Let $q$ be a prime power and $n > 0$. Let
$(d_0, m_0), \dots, (d_{k-1}, m_{k-1})$ be blocks with $d_i \ge 1$ and $m_i \ge 1$ for all $i$,
$d_0 > d_1 > \dots > d_{k-1}$ and $m_0 d_0 + \dots + m_{k-1} d_{k-1} = n$. Put
$p_i = \sum_{j < i} m_j d_j$, and let the basic dimension list be the concatenation, for
$i = 0, \dots, k - 1$ in order, of $\sum_{j=0}^{m_i - 1} q^{p_i + j d_i}$ copies of $d_i$. If this
list is nonincreasing, then every Gaussian partition whose dimension list equals it is a
restricted Gaussian partition for $q$ and $n$.

The witness realizes every block with an empty branch. -/
theorem basic_ancestor_is_restricted (q n : Nat) (blocks : List Block)
    (G : GaussianPartition) (hq : IsPrimePow q) (hn : 0 < n)
    (hvalid : BlocksStructValid blocks n)
    (hsorted : (basicGlobalDims q blocks).Pairwise (fun a b : Nat => a ≥ b))
    (hdims : G.dims = basicGlobalDims q blocks) :
    IsRestrictedGaussianPartition q n G := by
  have hrep : ∀ (m i : Nat),
      i < m → (List.replicate m ([] : List BranchStep))[i]? = some [] := by
    intro m
    induction m with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero i)
    | succ m ih =>
      intro i hi
      cases i with
      | zero => rfl
      | succ i => exact ih i (by omega)
  have hch : ∀ i, i < blocks.length →
      chainAt (List.replicate blocks.length []) i = [] := by
    intro i hi
    simp only [chainAt, hrep _ _ hi]
  have hfin : ∀ t, t ≤ blocks.length →
      allFinalDimsAux q blocks (List.replicate blocks.length []) t =
        some ((List.range t).map (blockBasicDims q blocks)) := by
    intro t
    induction t with
    | zero => intro _; rfl
    | succ t ih =>
      intro ht
      have hlt : t < blocks.length := by omega
      have hbt : blockFinalDims q blocks (List.replicate blocks.length []) t =
          some (blockBasicDims q blocks t) := by
        simp only [blockFinalDims, applyChain, hrep _ _ hlt]
      have ht' : t ≤ blocks.length := by omega
      have haux := ih ht'
      simp only [allFinalDimsAux, haux, hbt, List.range_succ, List.map_append,
        List.map_cons, List.map_nil]
  have hbranch : ∀ i, i < blocks.length →
      BranchValid q blocks i (chainAt (List.replicate blocks.length []) i) := by
    intro i hi
    rw [hch i hi]
    exact True.intro
  have hstage : ∀ i, i < blocks.length → ∀ k,
      k < (chainAt (List.replicate blocks.length []) i).length →
      (stageGlobalDims q blocks (List.replicate blocks.length [])
        (basicSegs q blocks) i k).all
        (fun g => decide (g.Pairwise (fun a b : Nat => a ≥ b))) = true := by
    intro i hi k hk
    have hnil : ([] : List BranchStep).length = 0 := rfl
    rw [hch i hi, hnil] at hk
    exact absurd hk (Nat.not_lt_zero k)
  refine ⟨hq, hn, blocks, List.replicate blocks.length ([] : List BranchStep),
    List.length_replicate, hvalid, hbranch, basicSegs q blocks, hfin _ le_rfl,
    hsorted, hsorted, hstage, hdims⟩

end

end MetaMathlibExt
