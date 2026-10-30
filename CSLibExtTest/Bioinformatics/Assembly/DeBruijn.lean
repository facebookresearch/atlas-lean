/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Assembly.DeBruijn
public meta import CSLibExt.Bioinformatics.Assembly.DeBruijn

/-!
# de Bruijn assembly tests

Executed fixtures: the `3`-mers and de Bruijn edges of `ACGCGT`; its `2`-mer walk, whose steps
are the edges in order and which spells the string back; a second Eulerian trail of the de Bruijn
multigraph of `TAATGCCATGGGATGTT` that spells a different string with the same `3`-mer
multiset; boundary cases (a string shorter than `k`, `k - 1 = |s|`). Closed checks: the
theorems instantiated. Each run throws on a disagreement.
-/

namespace Cslib.Bioinformatics.Assembly.DeBruijn

/-- `ACGCGT`. -/
def s₁ : List Char := "ACGCGT".toList

#guard kmers 3 s₁ = ["ACG", "CGC", "GCG", "CGT"].map String.toList
#guard deBruijnEdges 3 s₁ =
  [("AC", "CG"), ("CG", "GC"), ("GC", "CG"), ("CG", "GT")].map fun e => (e.1.toList, e.2.toList)
#guard (kmers 2 s₁).zip (kmers 2 s₁).tail = deBruijnEdges 3 s₁
#guard spell (kmers 2 s₁) = s₁

/-- `TAATGCCATGGGATGTT`: the vertex `TG` is visited three times, so its de Bruijn multigraph
has several Eulerian trails. -/
def s₃ : List Char := "TAATGCCATGGGATGTT".toList

/-- An Eulerian trail of the de Bruijn multigraph of `s₃` that differs from its own walk: the
two loops through `TG` are traversed in the other order. -/
def W₃ : List (List Char) :=
  ["TA", "AA", "AT", "TG", "GG", "GG", "GA", "AT", "TG", "GC", "CC", "CA", "AT", "TG", "GT",
    "TT"].map String.toList

#guard (W₃.zip W₃.tail).isPerm (deBruijnEdges 3 s₃)
#guard spell W₃ ≠ s₃
#guard (kmers 3 (spell W₃)).isPerm (kmers 3 s₃)

-- Boundary cases: shorter than `k`, and `k - 1 = |s|`.
#guard deBruijnEdges 3 "A".toList = []
#guard kmers 2 "AC".toList = ["AC".toList] ∧ spell (kmers 2 "AC".toList) = "AC".toList

-- The theorems, instantiated.
example : (kmers 2 s₁).zip (kmers 2 s₁).tail = deBruijnEdges 3 s₁ :=
  zip_tail_kmers 3 (by decide) s₁
example : spell (kmers 2 s₁) = s₁ := spell_kmers 3 (by decide) s₁ (by decide)

end Cslib.Bioinformatics.Assembly.DeBruijn
