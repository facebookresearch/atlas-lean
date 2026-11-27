/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import MathlibExt.Combinatorics.Coding.CycleShannonBounds
public import MathlibExt.Combinatorics.Coding.PolakSchrijver
public import MathlibExt.Combinatorics.Coding.CycleShannonBoundsBpz2026CycleTwentyOneConstruction
public import MathlibExt.Combinatorics.Coding.CycleShannonBoundsBpz2026CycleTwentyOneLowerBound
public import MathlibExt.Combinatorics.Coding.CycleShannonBoundsLovasz1979UpperBound
public import MathlibExt.Combinatorics.Coding.CycleShannonBoundsMathewOstergard2017LowerBound

/-!
# Known cycle-capacity construction and rate requests

These are private unproved requests, not proofs or conjectures about newly open results.
The actual modular code and capacity model comes from `CycleGraphCode`. The paper-specific
integer profiles below perform only arithmetic, using `BPZProfile`, `BPZProfile.star` and
`bpzProfileSquareIter`, which are now defined in
`MathlibExt.Combinatorics.Coding.CycleShannonBoundsBpz2026CycleTwentyOneConstruction`; they do
not supply independent sets or prove that a profile comes from a valid tuple. The
twenty-one-cycle lower bound `bpz2026CycleTwentyOneLowerBound` is proved in
`MathlibExt.Combinatorics.Coding.CycleShannonBoundsBpz2026CycleTwentyOneLowerBound`.

Source: Optimization Problems, constant 9a, pinned at
`2c1968cd520b60f1cf3cf50749f7285e800e4e15`; Gao arXiv:2607.27869;
Buys--Polak--Zuiddam arXiv:2607.29681; Tandon arXiv:2608.30273.
Approximate decimal displays are not asserted as equalities or rational bounds.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.Coding.CycleShannonBoundsWanted

open MathlibExt.Combinatorics.Coding.CycleGraphCode

/-- **Vesel–Žerovnik lower bound for the capacity of the 7-cycle.** The Shannon capacity of the
$7$-cycle is at least $108^{1/4}$.

Source: Vesel--Žerovnik (2002), exact rate row; no unprinted code is supplied. -/
theorem_wanted veselZerovnik2002LowerBound :
  ENNReal.rpow 108 ((4 : ℝ)⁻¹) ≤ shannonCapacityCycle 7

/-- **Itty–Rosin–Carstensen–Reichman lower bound for the capacity of the 7-cycle.** The Shannon
capacity of the $7$-cycle is at least $134753^{1/10}$, as an inequality in $[0, \infty]$.

Source: Itty--Rosin--Carstensen--Reichman, arXiv:2607.21517, exact tenth-root rate. -/
theorem_wanted ittyRosinCarstensenReichman2026LowerBound :
  ENNReal.rpow 134753 ((10 : ℝ)⁻¹) ≤ shannonCapacityCycle 7

/-- **Itty–Rosin–Carstensen–Reichman code of dimension 10 for the 7-cycle.** There is a finite
set $A$ of words of length $10$ over $\mathbb{Z}/7\mathbb{Z}$ that is an independent code for the
$7$-cycle and has exactly $134753$ elements.

Source: Itty--Rosin--Carstensen--Reichman, arXiv:2607.21517, tenth-power construction. -/
theorem_wanted ittyRosinCarstensenReichman2026Construction :
  ∃ A : Finset (Fin 10 → ZMod 7), IsCycleCode 7 A ∧ A.card = 134753

set_option linter.style.longLine false in
/-- **Gao's code size in dimension 200.** $M_{40}$ is the natural number
$4085567963379990282748597333793399773399910167372462
112610203714626938509773125898252337545387866277249$,
the cardinality Gao prints for a code of length $200$ for the $7$-cycle.

Source: Gao, arXiv:2607.27869, the printed M40 value. -/
def gao2026M40 : ℕ :=
  4085567963379990282748597333793399773399910167372462112610203714626938509773125898252337545387866277249

/-- **Gao's code of dimension 200 for the 7-cycle.** Let $M_{40}$ be Gao's printed dimension-200
cardinality, a natural number with 103 decimal digits. There is a finite set $A$ of words of
length $200$ over $\mathbb{Z}/7\mathbb{Z}$ that is an independent code for the $7$-cycle and has
exactly $M_{40}$ elements.

Source: Gao, arXiv:2607.27869, exact dimension-200 construction. -/
theorem_wanted gao2026Construction :
  ∃ A : Finset (Fin 200 → ZMod 7), IsCycleCode 7 A ∧ A.card = gao2026M40

/-- **Gao's lower bound for the capacity of the 7-cycle.** Let $M_{40}$ be Gao's printed
dimension-200 cardinality, a natural number with 103 decimal digits. The Shannon capacity of the
$7$-cycle is at least $M_{40}^{1/200}$, as an inequality in $[0, \infty]$.

Source: Gao, arXiv:2607.27869, exact dimension-200 root rate. -/
theorem_wanted gao2026LowerBound :
  ENNReal.rpow (gao2026M40 : ENNReal) ((200 : ℝ)⁻¹) ≤ shannonCapacityCycle 7

/-- **Buys–Polak–Zuiddam one-block profile for the 7-cycle.** This is the Buys–Polak–Zuiddam
(BPZ) profile whose code, pairs, auxiliary and neutral coordinates are $367$, $8$, $367$ and $322$.

Only these four integers are recorded, not BPZ's five-dimensional construction behind them.

Source: BPZ, arXiv:2607.29681, seven-cycle construction. -/
def bpzC7Pi1 : BPZProfile := ⟨367, 8, 367, 322⟩
/-- **Buys–Polak–Zuiddam two-block profile for the 7-cycle.** This is $p_1 \star p_1$, where $p_1$
is the one-block 7-cycle profile, whose code, pairs, auxiliary and neutral coordinates are $367$,
$8$, $367$ and $322$, and $\star$ is the Buys–Polak–Zuiddam (BPZ) profile product.

Source: BPZ, arXiv:2607.29681, seven-cycle construction. -/
def bpzC7Pi2 : BPZProfile := bpzC7Pi1.star bpzC7Pi1
/-- **Three-block BPZ seven-cycle profile.** A BPZ profile is a quadruple of integers
(code, pairs, auxiliary, neutral), and $\star$ denotes the BPZ profile product. The three-block
seven-cycle profile of Buys–Polak–Zuiddam is $\pi_3 = \pi_1 \star \pi_2$, where
$\pi_1 = (367, 8, 367, 322)$ is the one-block profile and $\pi_2 = \pi_1 \star \pi_1$ is the
two-block profile.

Source: BPZ, arXiv:2607.29681, seven-cycle construction. -/
def bpzC7Pi3 : BPZProfile := bpzC7Pi1.star bpzC7Pi2
/-- **Five-block BPZ seven-cycle profile.** A BPZ profile is a quadruple of integers
(code, pairs, auxiliary, neutral), and $\star$ denotes the BPZ profile product. The five-block
seven-cycle profile of Buys–Polak–Zuiddam is $\pi_5 = \pi_2 \star \pi_3$, where
$\pi_1 = (367, 8, 367, 322)$, $\pi_2 = \pi_1 \star \pi_1$ and $\pi_3 = \pi_1 \star \pi_2$ are
the one-, two- and three-block profiles.

Source: BPZ, arXiv:2607.29681, seven-cycle construction. -/
def bpzC7Pi5 : BPZProfile := bpzC7Pi2.star bpzC7Pi3
/-- **Buys–Polak–Zuiddam ten-block profile for the 7-cycle.** This is $p_5 \star p_5$, where $p_5$
is the five-block 7-cycle profile and $\star$ is the Buys–Polak–Zuiddam (BPZ) profile product.

Source: BPZ, arXiv:2607.29681, seven-cycle construction. -/
def bpzC7Pi10 : BPZProfile := bpzC7Pi5.star bpzC7Pi5
/-- **Buys–Polak–Zuiddam twenty-block profile for the 7-cycle.** This is $p_{10} \star p_{10}$,
where $p_{10}$ is the ten-block 7-cycle profile and $\star$ is the Buys–Polak–Zuiddam (BPZ)
profile product.

Source: BPZ, arXiv:2607.29681, seven-cycle construction. -/
def bpzC7Pi20 : BPZProfile := bpzC7Pi10.star bpzC7Pi10
/-- **Forty-block BPZ seven-cycle profile.** A BPZ profile is a quadruple of integers
(code, pairs, auxiliary, neutral), and $\star$ denotes the BPZ profile product. The final
forty-block seven-cycle profile of Buys–Polak–Zuiddam is $\pi_{40} = \pi_{20} \star \pi_{20}$,
where $\pi_1 = (367, 8, 367, 322)$, $\pi_2 = \pi_1 \star \pi_1$, $\pi_3 = \pi_1 \star \pi_2$,
$\pi_5 = \pi_2 \star \pi_3$, $\pi_{10} = \pi_5 \star \pi_5$ and
$\pi_{20} = \pi_{10} \star \pi_{10}$.

Source: BPZ, arXiv:2607.29681, seven-cycle construction. -/
def bpzC7Pi40 : BPZProfile := bpzC7Pi20.star bpzC7Pi20

set_option linter.style.longLine false in
/-- **Code coordinate of the forty-block BPZ seven-cycle profile.** The code coordinate (the
first of the four integer coordinates) of the forty-block seven-cycle profile $\pi_{40}$ of
Buys–Polak–Zuiddam equals
$4089635995108338053456272492117641008738901835089431264388780413340766441486608
118807897325023935704961$.

Source: BPZ, arXiv:2607.29681, forty-block seven-cycle recursion. -/
theorem bpzC7Pi40_code :
    bpzC7Pi40.code =
      4089635995108338053456272492117641008738901835089431264388780413340766441486608118807897325023935704961 := by
  rfl

/-- **Buys–Polak–Zuiddam code for the 7-cycle in length 200.** Let $c$ be the code coordinate
of BPZ's final forty-block seven-cycle profile, and let $M = \max(c, 0)$. There is a finite set
of words of length $200$ over $\mathbb{Z}/7\mathbb{Z}$ that is an independent code for the
$7$-cycle and has exactly $M$ elements.

Source: BPZ, arXiv:2607.29681, the exact forty-block dimension-200 construction. -/
theorem_wanted bpz2026CycleSevenConstruction :
  ∃ A : Finset (Fin 200 → ZMod 7), IsCycleCode 7 A ∧ A.card = bpzC7Pi40.code.toNat

/-- **Buys–Polak–Zuiddam lower bound for the capacity of the 7-cycle.** Let $c$ be the code
coordinate of BPZ's final forty-block seven-cycle profile, and let $M = \max(c, 0)$. Then
$M^{1/200}$ is at most the Shannon capacity of the $7$-cycle, as an inequality in $[0, \infty]$.

Source: BPZ, arXiv:2607.29681, the exact dimension-200 root rate. -/
theorem_wanted bpz2026CycleSevenLowerBound :
  ENNReal.rpow (bpzC7Pi40.code.toNat : ENNReal) ((200 : ℝ)⁻¹) ≤ shannonCapacityCycle 7

set_option linter.style.longLine false in
/-- **Tandon's dimension-500 code size.** Tandon's dimension-500 code size is the natural number
$M^*$ with $257$ decimal digits given by
$$
M^* = 33964672918117456943408517573718333225317390754651100605971152590324909277046876400440
35395842835926298962152039473727668119665577675838633047083277330855915999031707610213
1413374061066595834823529274560988950698158729501949866486079791784996498585401881281
$$

Source: Tandon, arXiv:2608.30273, the printed Mstar value. -/
def tandon2026Mstar : ℕ :=
  33964672918117456943408517573718333225317390754651100605971152590324909277046876400440353958428359262989621520394737276681196655776758386330470832773308559159990317076102131413374061066595834823529274560988950698158729501949866486079791784996498585401881281

/-- **Tandon's dimension-500 code for the 7-cycle.** Let $M^*$ be Tandon's dimension-500 code
size. There is an independent code for the $7$-cycle consisting of words of length $500$ over
$\mathbb{Z}/7\mathbb{Z}$ with exactly $M^*$ codewords.

Source: Tandon, arXiv:2608.30273, exact dimension-500 construction. -/
theorem_wanted tandon2026Construction :
  ∃ A : Finset (Fin 500 → ZMod 7), IsCycleCode 7 A ∧ A.card = tandon2026Mstar

/-- **Tandon's lower bound for the capacity of the 7-cycle.** Let $M^*$ be Tandon's
dimension-500 code size. The Shannon capacity of the $7$-cycle is at least $(M^*)^{1/500}$.

Source: Tandon, arXiv:2608.30273, exact dimension-500 root rate. -/
theorem_wanted tandon2026LowerBound :
  ENNReal.rpow (tandon2026Mstar : ENNReal) ((500 : ℝ)⁻¹) ≤ shannonCapacityCycle 7

/-- **One-block BPZ profile for the 11-cycle.** The one-block eleven-cycle profile of Buys,
Polak and Zuiddam is the profile with code coordinate $148$, pairs coordinate $3$, auxiliary
coordinate $148$ and neutral coordinate $142$.

In the source this profile comes from a construction in dimension $3$; that origin is not
checked here.

Source: BPZ, arXiv:2607.29681, eleven-cycle construction. -/
def bpzC11Pi1 : BPZProfile := ⟨148, 3, 148, 142⟩
/-- **Two-block BPZ profile for the 11-cycle.** The two-block eleven-cycle profile of Buys,
Polak and Zuiddam is the profile product $\pi_1 \star \pi_1$, where $\pi_1$ is their one-block
eleven-cycle profile.

Source: BPZ, arXiv:2607.29681, eleven-cycle construction. -/
def bpzC11Pi2 : BPZProfile := bpzC11Pi1.star bpzC11Pi1
/-- **Three-block BPZ profile for the 11-cycle.** The three-block eleven-cycle profile of Buys,
Polak and Zuiddam is the profile product $\pi_1 \star \pi_2$, where $\pi_1$ and $\pi_2$ are
their one-block and two-block eleven-cycle profiles.

Source: BPZ, arXiv:2607.29681, eleven-cycle construction. -/
def bpzC11Pi3 : BPZProfile := bpzC11Pi1.star bpzC11Pi2
/-- **Four-block BPZ profile for the 11-cycle.** The four-block eleven-cycle profile of Buys,
Polak and Zuiddam is the profile product $\pi_2 \star \pi_2$, where $\pi_2$ is their two-block
eleven-cycle profile.

Source: BPZ, arXiv:2607.29681, eleven-cycle construction. -/
def bpzC11Pi4 : BPZProfile := bpzC11Pi2.star bpzC11Pi2
/-- **Seven-block BPZ profile for the 11-cycle.** The seven-block eleven-cycle profile of Buys,
Polak and Zuiddam is the profile product $\pi_3 \star \pi_4$, where $\pi_3$ and $\pi_4$ are
their three-block and four-block eleven-cycle profiles.

Source: BPZ, arXiv:2607.29681, eleven-cycle construction. -/
def bpzC11Pi7 : BPZProfile := bpzC11Pi3.star bpzC11Pi4
/-- **Eight-block BPZ profile of the eleven-cycle.** The eight-block BPZ profile of the
eleven-cycle is $\pi_4 \star \pi_4$, where $\pi_4$ is the four-block BPZ profile of the
eleven-cycle and $\star$ is the BPZ profile product.

Source: BPZ, arXiv:2607.29681, eleven-cycle construction. -/
def bpzC11Pi8 : BPZProfile := bpzC11Pi4.star bpzC11Pi4
/-- **Fourteen-block BPZ profile for the 11-cycle.** The fourteen-block eleven-cycle profile of
Buys, Polak and Zuiddam is the profile product $\pi_7 \star \pi_7$, where $\pi_7$ is their
seven-block eleven-cycle profile.

Source: BPZ, arXiv:2607.29681, eleven-cycle construction. -/
def bpzC11Pi14 : BPZProfile := bpzC11Pi7.star bpzC11Pi7
/-- **Fifteen-block BPZ profile for the 11-cycle.** The fifteen-block eleven-cycle profile of
Buys, Polak and Zuiddam is the profile product $\pi_7 \star \pi_8$, where $\pi_7$ and $\pi_8$
are their seven-block and eight-block eleven-cycle profiles.

Source: BPZ, arXiv:2607.29681, eleven-cycle construction. -/
def bpzC11Pi15 : BPZProfile := bpzC11Pi7.star bpzC11Pi8
/-- **Twenty-nine-block BPZ profile for the 11-cycle.** The twenty-nine-block eleven-cycle
profile of Buys, Polak and Zuiddam is the profile product $\pi_{14} \star \pi_{15}$, where
$\pi_{14}$ and $\pi_{15}$ are their fourteen-block and fifteen-block eleven-cycle profiles.

Source: BPZ, arXiv:2607.29681, eleven-cycle construction. -/
def bpzC11Pi29 : BPZProfile := bpzC11Pi14.star bpzC11Pi15
/-- **Fifty-eight-block BPZ profile for the 11-cycle.** The final fifty-eight-block eleven-cycle
profile of Buys, Polak and Zuiddam is the profile product $\pi_{29} \star \pi_{29}$, where
$\pi_{29}$ is their twenty-nine-block eleven-cycle profile.

Source: BPZ, arXiv:2607.29681, eleven-cycle construction. -/
def bpzC11Pi58 : BPZProfile := bpzC11Pi29.star bpzC11Pi29

/-- **One-block BPZ profile of the thirteen-cycle.** The one-block BPZ profile of the
thirteen-cycle is the BPZ profile with code coordinate $62530$, pairs coordinate $1014$,
auxiliary coordinate $62530$ and neutral coordinate $60502$.

BPZ describe it as their one-block six-dimensional thirteen-cycle profile.

Source: BPZ, arXiv:2607.29681, thirteen-cycle construction. -/
def bpzC13Pi1 : BPZProfile := ⟨62530, 1014, 62530, 60502⟩
/-- **Two-block BPZ profile of the thirteen-cycle.** The two-block BPZ profile of the
thirteen-cycle is $\pi_1 \star \pi_1$, where $\pi_1$ is the one-block BPZ profile of the
thirteen-cycle and $\star$ is the BPZ profile product.

Source: BPZ, arXiv:2607.29681, thirteen-cycle construction. -/
def bpzC13Pi2 : BPZProfile := bpzC13Pi1.star bpzC13Pi1
/-- **Three-block BPZ profile of the thirteen-cycle.** The three-block BPZ profile of the
thirteen-cycle is $\pi_1 \star \pi_2$, where $\pi_1$ and $\pi_2$ are the one-block and two-block
BPZ profiles of the thirteen-cycle and $\star$ is the BPZ profile product.

Source: BPZ, arXiv:2607.29681, thirteen-cycle construction. -/
def bpzC13Pi3 : BPZProfile := bpzC13Pi1.star bpzC13Pi2
/-- **Four-block BPZ profile of the thirteen-cycle.** The four-block BPZ profile of the
thirteen-cycle is $\pi_2 \star \pi_2$, where $\pi_2$ is the two-block BPZ profile of the
thirteen-cycle and $\star$ is the BPZ profile product.

Source: BPZ, arXiv:2607.29681, thirteen-cycle construction. -/
def bpzC13Pi4 : BPZProfile := bpzC13Pi2.star bpzC13Pi2
/-- **Five-block BPZ profile of the thirteen-cycle.** The five-block BPZ profile of the
thirteen-cycle is $\pi_2 \star \pi_3$, where $\pi_2$ and $\pi_3$ are the two-block and three-block
BPZ profiles of the thirteen-cycle and $\star$ is the BPZ profile product.

Source: BPZ, arXiv:2607.29681, thirteen-cycle construction. -/
def bpzC13Pi5 : BPZProfile := bpzC13Pi2.star bpzC13Pi3
/-- **Nine-block BPZ profile of the thirteen-cycle.** The nine-block BPZ profile of the
thirteen-cycle is $\pi_4 \star \pi_5$, where $\pi_4$ and $\pi_5$ are the four-block and five-block
BPZ profiles of the thirteen-cycle and $\star$ is the BPZ profile product.

Source: BPZ, arXiv:2607.29681, thirteen-cycle construction. -/
def bpzC13Pi9 : BPZProfile := bpzC13Pi4.star bpzC13Pi5
/-- **Seventy-two-block BPZ profile of the thirteen-cycle.** Let $\pi_9$ be the nine-block BPZ
profile of the thirteen-cycle, and let $\star$ be the BPZ profile product. Set
$\sigma_0 = \pi_9$ and $\sigma_{k+1} = \sigma_k \star \sigma_k$. The seventy-two-block BPZ profile
of the thirteen-cycle is $\sigma_3$, the result of squaring $\pi_9$ three times.

This is the final profile of BPZ's thirteen-cycle construction.

Source: BPZ, arXiv:2607.29681, thirteen-cycle construction. -/
def bpzC13Pi72 : BPZProfile := bpzProfileSquareIter 3 bpzC13Pi9

/-- **One-block BPZ profile of the fifteen-cycle.** The one-block BPZ profile of the
fifteen-cycle is the BPZ profile with code coordinate $2842$, pairs coordinate $3$, auxiliary
coordinate $2842$ and neutral coordinate $2833$.

BPZ describe it as their one-block four-dimensional fifteen-cycle profile.

Source: BPZ, arXiv:2607.29681, fifteen-cycle construction. -/
def bpzC15Pi1 : BPZProfile := ⟨2842, 3, 2842, 2833⟩
/-- **BPZ profile of the fifteen-cycle after ten squarings.** Let $\pi_1$ be the one-block BPZ
profile of the fifteen-cycle, and let $\star$ be the BPZ profile product. Set $\sigma_0 = \pi_1$
and $\sigma_{k+1} = \sigma_k \star \sigma_k$. This profile is $\sigma_{10}$, the result of
squaring $\pi_1$ ten times.

This is the final profile of BPZ's fifteen-cycle construction.

Source: BPZ, arXiv:2607.29681, fifteen-cycle construction. -/
def bpzC15Pi1024 : BPZProfile := bpzProfileSquareIter 10 bpzC15Pi1

/-- **Buys–Polak–Zuiddam one-block profile for the 19-cycle.** This is the Buys–Polak–Zuiddam
(BPZ) profile whose code, pairs, auxiliary and neutral coordinates are $7666$, $2$, $7666$
and $7661$.

Only these four integers are recorded, not BPZ's four-dimensional construction behind them.

Source: BPZ, arXiv:2607.29681, nineteen-cycle construction. -/
def bpzC19Pi1 : BPZProfile := ⟨7666, 2, 7666, 7661⟩
/-- **Buys–Polak–Zuiddam 4096-block profile for the 19-cycle.** Let $p_0$ be the one-block
19-cycle profile, whose code, pairs, auxiliary and neutral coordinates are $7666$, $2$,
$7666$ and $7661$, and let $p_{j+1} = p_j \star p_j$, where $\star$ is the
Buys–Polak–Zuiddam (BPZ) profile product. This profile is $p_{12}$, the result of squaring
$p_0$ twelve times.

Source: BPZ, arXiv:2607.29681, nineteen-cycle construction. -/
def bpzC19Pi4096 : BPZProfile := bpzProfileSquareIter 12 bpzC19Pi1

/-- **Buys–Polak–Zuiddam one-block profile for the 23-cycle.** This is the Buys–Polak–Zuiddam
(BPZ) profile whose code, pairs, auxiliary and neutral coordinates are $16466$, $30$,
$16466$ and $16323$.

Only these four integers are recorded, not BPZ's four-dimensional construction behind them.

Source: BPZ, arXiv:2607.29681, twenty-three-cycle construction. -/
def bpzC23Pi1 : BPZProfile := ⟨16466, 30, 16466, 16323⟩
/-- **Buys–Polak–Zuiddam 512-block profile for the 23-cycle.** Let $p_0$ be the one-block
23-cycle profile, whose code, pairs, auxiliary and neutral coordinates are $16466$, $30$,
$16466$ and $16323$, and let $p_{j+1} = p_j \star p_j$, where $\star$ is the
Buys–Polak–Zuiddam (BPZ) profile product. This profile is $p_9$, the result of squaring
$p_0$ nine times.

Source: BPZ, arXiv:2607.29681, twenty-three-cycle construction. -/
def bpzC23Pi512 : BPZProfile := bpzProfileSquareIter 9 bpzC23Pi1

/-- **Buys–Polak–Zuiddam code for the eleven-cycle in dimension 174.** Let $c$ be the code
coordinate of the fifty-eight-block eleven-cycle profile $\pi_{58}$ of Buys–Polak–Zuiddam. There
is a finite set of words of length $174$ over $\mathbb{Z}/11\mathbb{Z}$ that is an independent
code for the $11$-cycle and has exactly $\max(c, 0)$ elements.

Source: BPZ, arXiv:2607.29681, eleven-cycle construction in dimension 174. -/
theorem_wanted bpz2026CycleElevenConstruction :
  ∃ A : Finset (Fin 174 → ZMod 11), IsCycleCode 11 A ∧ A.card = bpzC11Pi58.code.toNat

/-- **Buys–Polak–Zuiddam code for the 13-cycle in length 432.** Let $c$ be the code coordinate
of BPZ's final seventy-two-block thirteen-cycle profile, and let $M = \max(c, 0)$. There is a
finite set of words of length $432$ over $\mathbb{Z}/13\mathbb{Z}$ that is an independent code
for the $13$-cycle and has exactly $M$ elements.

Source: BPZ, arXiv:2607.29681, thirteen-cycle construction in dimension 432. -/
theorem_wanted bpz2026CycleThirteenConstruction :
  ∃ A : Finset (Fin 432 → ZMod 13), IsCycleCode 13 A ∧ A.card = bpzC13Pi72.code.toNat

/-- **Buys–Polak–Zuiddam code for the fifteen-cycle in dimension 4096.** Let $c$ be the code
coordinate of the $1024$-block fifteen-cycle profile $\pi_{1024}$ of Buys–Polak–Zuiddam. There is
a finite set of words of length $4096$ over $\mathbb{Z}/15\mathbb{Z}$ that is an independent code
for the $15$-cycle and has exactly $\max(c, 0)$ elements.

Source: BPZ, arXiv:2607.29681, fifteen-cycle construction in dimension 4096. -/
theorem_wanted bpz2026CycleFifteenConstruction :
  ∃ A : Finset (Fin 4096 → ZMod 15), IsCycleCode 15 A ∧ A.card = bpzC15Pi1024.code.toNat

/-- **Buys–Polak–Zuiddam code for the nineteen-cycle in dimension 16384.** Let $c$ be the code
coordinate of the $4096$-block nineteen-cycle profile $\pi_{4096}$ of Buys–Polak–Zuiddam. There
is a finite set of words of length $16384$ over $\mathbb{Z}/19\mathbb{Z}$ that is an independent
code for the $19$-cycle and has exactly $\max(c, 0)$ elements.

Source: BPZ, arXiv:2607.29681, nineteen-cycle construction in dimension 16384. -/
theorem_wanted bpz2026CycleNineteenConstruction :
  ∃ A : Finset (Fin 16384 → ZMod 19), IsCycleCode 19 A ∧ A.card = bpzC19Pi4096.code.toNat

/-- **Buys–Polak–Zuiddam code for the 23-cycle in length 2048.** Let $c$ be the code coordinate
of BPZ's final twenty-three-cycle profile after nine squarings, and let $M = \max(c, 0)$. There
is a finite set of words of length $2048$ over $\mathbb{Z}/23\mathbb{Z}$ that is an independent
code for the $23$-cycle and has exactly $M$ elements.

Source: BPZ, arXiv:2607.29681, twenty-three-cycle construction in dimension 2048. -/
theorem_wanted bpz2026CycleTwentyThreeConstruction :
  ∃ A : Finset (Fin 2048 → ZMod 23), IsCycleCode 23 A ∧ A.card = bpzC23Pi512.code.toNat

/-- **Buys–Polak–Zuiddam lower bound for the capacity of the eleven-cycle.** Let $c$ be the code
coordinate of the fifty-eight-block eleven-cycle profile $\pi_{58}$ of Buys–Polak–Zuiddam. Then
$\max(c, 0)^{1/174}$ is at most the Shannon capacity of the $11$-cycle, as an inequality in
$[0, \infty]$.

Source: BPZ, arXiv:2607.29681, exact eleven-cycle root rate. -/
theorem_wanted bpz2026CycleElevenLowerBound :
  ENNReal.rpow (bpzC11Pi58.code.toNat : ENNReal) ((174 : ℝ)⁻¹) ≤ shannonCapacityCycle 11

/-- **Buys–Polak–Zuiddam lower bound for the capacity of the 13-cycle.** Let $c$ be the code
coordinate of BPZ's final seventy-two-block thirteen-cycle profile, and let $M = \max(c, 0)$.
Then $M^{1/432}$ is at most the Shannon capacity of the $13$-cycle, as an inequality in
$[0, \infty]$.

Source: BPZ, arXiv:2607.29681, exact thirteen-cycle root rate. -/
theorem_wanted bpz2026CycleThirteenLowerBound :
  ENNReal.rpow (bpzC13Pi72.code.toNat : ENNReal) ((432 : ℝ)⁻¹) ≤ shannonCapacityCycle 13

/-- **Buys–Polak–Zuiddam lower bound for the capacity of the fifteen-cycle.** Let $c$ be the
code coordinate of the $1024$-block fifteen-cycle profile $\pi_{1024}$ of Buys–Polak–Zuiddam.
Then $\max(c, 0)^{1/4096}$ is at most the Shannon capacity of the $15$-cycle, as an inequality
in $[0, \infty]$.

Source: BPZ, arXiv:2607.29681, exact fifteen-cycle root rate. -/
theorem_wanted bpz2026CycleFifteenLowerBound :
  ENNReal.rpow (bpzC15Pi1024.code.toNat : ENNReal) ((4096 : ℝ)⁻¹) ≤ shannonCapacityCycle 15

/-- **Buys–Polak–Zuiddam lower bound for the capacity of the 19-cycle.** Let $c$ be the code
coordinate of BPZ's final nineteen-cycle profile after twelve squarings, and let
$M = \max(c, 0)$. Then $M^{1/16384}$ is at most the Shannon capacity of the $19$-cycle, as an
inequality in $[0, \infty]$.

Source: BPZ, arXiv:2607.29681, exact nineteen-cycle root rate. -/
theorem_wanted bpz2026CycleNineteenLowerBound :
  ENNReal.rpow (bpzC19Pi4096.code.toNat : ENNReal) ((16384 : ℝ)⁻¹) ≤ shannonCapacityCycle 19

/-- **Buys–Polak–Zuiddam lower bound for the capacity of the 23-cycle.** Let $c$ be the code
coordinate of BPZ's final twenty-three-cycle profile after nine squarings, and let
$M = \max(c, 0)$. Then $M^{1/2048}$ is at most the Shannon capacity of the $23$-cycle, as an
inequality in $[0, \infty]$.

Source: BPZ, arXiv:2607.29681, exact twenty-three-cycle root rate. -/
theorem_wanted bpz2026CycleTwentyThreeLowerBound :
  ENNReal.rpow (bpzC23Pi512.code.toNat : ENNReal) ((2048 : ℝ)⁻¹) ≤ shannonCapacityCycle 23

end MathlibExt.Combinatorics.Coding.CycleShannonBoundsWanted
