/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Real.Sqrt
public import MathlibExt.NumberTheory.ErdosMinimumOverlapConstant

@[expose] public section

namespace MathlibExt.NumberTheory.ErdosMinimumOverlapConstantWanted

/-!
Source: Optimization Problems, Constant 1b, frozen at commit
`2c1968cd520b60f1cf3cf50749f7285e800e4e15`, `constants/1b.md`, SHA-256
`1c51678108c90a2e841e1b49fa97940e4e1870324e1d949ddcb5b4345a0153ec`.
The source gives an optimization problem with known bounds and a known discrete
equivalence, but no supported exact-value conjecture. The half upper bound is
proved in the upstream model; the seventeen other claims are explicit
`theorem_wanted` declarations.
The decimal payloads are literal source requests, not certified rounded bounds.
Full primary-paper and numerical-certificate verification remains deferred.
-/

/-- **The proposition that $M(N)/N$ tends to $C_{1b}$.** For a natural number $N$ let $M(N)$ be
the Erdős minimum overlap function: the least, over all pairs of disjoint finite sets
$A, B \subseteq \mathbb{Z}$ with $A \cup B = \{1, \dots, 2N\}$ and $|A| = |B|$, of the largest
number of pairs $(a, b) \in A \times B$ with a given difference $a - b$. This is the proposition
that $M(N)/N$ tends to the continuous Erdős minimum-overlap constant $C_{1b}$ as $N \to \infty$.

Source: Haugland 2016; Optimization Problems, Constant 1b. -/
def continuousDiscreteEquivalence : Prop :=
  Filter.Tendsto MinOverlapQuotient Filter.atTop (nhds C₁ᵦ)

/-- **The proposition that $C_{1b}$ is the largest asymptotic overlap constant.** Call a real
number $c$ a universal asymptotic lower bound when for every $\varepsilon > 0$ there is a
positive integer $N_0$ such that for every $N \ge N_0$ and all disjoint finite sets
$A, B \subseteq \mathbb{Z}$ with $A \cup B = \{1, \dots, 2N\}$ and $|A| = |B|$, some integer $x$
satisfies $(c - \varepsilon) N \le \#\{(a, b) \in A \times B : a - b = x\}$. This is the
proposition that the continuous Erdős minimum-overlap constant $C_{1b}$ is a universal asymptotic
lower bound and that every universal asymptotic lower bound $c$ satisfies $c \le C_{1b}$.

Source: Haugland 2016; Optimization Problems, Constant 1b. -/
def continuousDiscreteAsymptoticCharacterization : Prop :=
  IsGreatest {c : ℝ | DiscreteUniversalLowerBound c} C₁ᵦ

/-- **Erdős's upper bound $1/2$ for the minimum-overlap constant (statement).** The statement that
the continuous Erdős minimum-overlap constant $C_{1b}$ satisfies $C_{1b} \le 1/2$.

Source: Erdős 1955; Optimization Problems, Constant 1b. -/
def upperBound_E1955_half : Prop := C₁ᵦ ≤ (1 : ℝ) / 2

/-- **Erdős's unpublished upper bound $4/9$ for the minimum-overlap constant (statement).** The
statement that the continuous Erdős minimum-overlap constant $C_{1b}$ satisfies $C_{1b} \le 4/9$.

Source: Erdős, unpublished; Optimization Problems, Constant 1b. -/
def upperBound_Erdos_unpublished_fourNinths : Prop := C₁ᵦ ≤ (4 : ℝ) / 9

/-- **Statement of the Motzkin–Ralston–Selfridge upper bound $5/12$ for the minimum-overlap
constant.** The proposition that the continuous Erdős minimum-overlap constant $C_{1b}$
satisfies $C_{1b} \le 5/12$.

Source: Motzkin--Ralston--Selfridge 1956; Optimization Problems, Constant 1b. -/
def upperBound_MRS1956_fiveTwelfths : Prop := C₁ᵦ ≤ (5 : ℝ) / 12

/-- **Statement of the Motzkin–Ralston–Selfridge upper bound $0.4$ for the minimum-overlap
constant.** The proposition that the continuous Erdős minimum-overlap constant $C_{1b}$
satisfies $C_{1b} \le 0.4$.

Source: Motzkin--Ralston--Selfridge 1956; Optimization Problems, Constant 1b. -/
def upperBound_MRS1956_pointFour : Prop := C₁ᵦ ≤ (4 : ℝ) / 10

/-- **Statement of Haugland's unpublished 1993 upper bound for the minimum-overlap constant.**
The proposition that the continuous Erdős minimum-overlap constant $C_{1b}$ satisfies
$C_{1b} \le 0.385694$.

Source: Haugland, unpublished 1993; Optimization Problems, Constant 1b. -/
def upperBound_Haugland_unpublished_1993 : Prop := C₁ᵦ ≤ (385694 : ℝ) / 1000000

/-- **Statement of Haugland's 1996 upper bound for the minimum-overlap constant.** The
proposition that the continuous Erdős minimum-overlap constant $C_{1b}$ satisfies
$C_{1b} \le 0.382002$.

Source: Haugland 1996; Optimization Problems, Constant 1b. -/
def upperBound_H1996 : Prop := C₁ᵦ ≤ (382002 : ℝ) / 1000000

/-- **Statement of Haugland's 2016 upper bound for the minimum-overlap constant.** The
proposition that the continuous Erdős minimum-overlap constant $C_{1b}$ satisfies
$C_{1b} \le 0.380926$.

Source: Haugland 2016; Optimization Problems, Constant 1b. -/
def upperBound_H2016 : Prop := C₁ᵦ ≤ (380926 : ℝ) / 1000000

/-- **AlphaEvolve upper bound for the minimum-overlap constant (statement).** The statement that
the continuous Erdős minimum-overlap constant $C_{1b}$ satisfies $C_{1b} \le 0.380924$.

Source: Georgiev--Gómez-Serrano--Tao--Wagner 2025; Optimization Problems, Constant 1b. -/
def upperBound_GGSWT2025_AlphaEvolve : Prop := C₁ᵦ ≤ (380924 : ℝ) / 1000000

/-- **TTT-Discover 2026 upper bound statement for the minimum overlap constant.** This is the
proposition that the continuous Erdős minimum-overlap constant $C_{1b}$ is at most $0.380876$.

Source: Yuksekgonul et al. 2026 (TTT-Discover); Optimization Problems, Constant 1b. -/
def upperBound_YKLBMWKCZGS2026_TTTDiscover : Prop := C₁ᵦ ≤ (380876 : ℝ) / 1000000

/-- **Together AI 2026 upper bound statement for the minimum overlap constant.** This is the
proposition that the continuous Erdős minimum-overlap constant $C_{1b}$ is at most $0.380871$.

Source: Together AI 2026; Optimization Problems, Constant 1b. -/
def upperBound_T2026_TogetherAI : Prop := C₁ᵦ ≤ (380871 : ℝ) / 1000000

/-- **SimpleTES 2026 upper bound statement for the minimum overlap constant.** This is the
proposition that the continuous Erdős minimum-overlap constant $C_{1b}$ is at most $0.380868$.

Source: Ye et al. 2026 (SimpleTES); Optimization Problems, Constant 1b. -/
def upperBound_YLTLYSTYLLGDHZSWZSHMELCZX2026_SimpleTES : Prop :=
  C₁ᵦ ≤ (380868 : ℝ) / 1000000

/-- **The proposition $1/4 \le C_{1b}$.** This is the proposition that the continuous Erdős
minimum-overlap constant $C_{1b}$ satisfies $1/4 \le C_{1b}$.

Source: Erdős 1955; Optimization Problems, Constant 1b. -/
def lowerBound_E1955_quarter : Prop := (1 : ℝ) / 4 ≤ C₁ᵦ

/-- **Scherk's lower bound for the minimum-overlap constant (statement).** The statement that the
continuous Erdős minimum-overlap constant $C_{1b}$ satisfies $1 - 1/\sqrt{2} \le C_{1b}$.

Source: Scherk, unpublished 1955; Optimization Problems, Constant 1b. -/
def lowerBound_Scherk_unpublished_1955 : Prop := 1 - 1 / Real.sqrt 2 ≤ C₁ᵦ

/-- **The proposition $(4 - \sqrt{6})/5 \le C_{1b}$.** This is the proposition that the continuous
Erdős minimum-overlap constant $C_{1b}$ satisfies $(4 - \sqrt{6})/5 \le C_{1b}$.

Source: Swierczkowski 1958; Optimization Problems, Constant 1b. -/
def lowerBound_S1958 : Prop := (4 - Real.sqrt 6) / 5 ≤ C₁ᵦ

/-- **The proposition $\sqrt{4 - \sqrt{15}} \le C_{1b}$.** This is the proposition that the
continuous Erdős minimum-overlap constant $C_{1b}$ satisfies $\sqrt{4 - \sqrt{15}} \le C_{1b}$.

Source: Moser 1959; Optimization Problems, Constant 1b. -/
def lowerBound_M1959 : Prop := Real.sqrt (4 - Real.sqrt 15) ≤ C₁ᵦ

/-- **White's lower bound for the minimum-overlap constant (statement).** The statement that the
continuous Erdős minimum-overlap constant $C_{1b}$ satisfies $0.379005 \le C_{1b}$, where
$0.379005$ is the exact rational number $379005/1000000$.

Source: White 2022; Optimization Problems, Constant 1b. -/
def lowerBound_W2022 : Prop := (379005 : ℝ) / 1000000 ≤ C₁ᵦ

/-- **The normalized minimum overlap tends to $C_{1b}$.** For a natural number $N$ let $M(N)$ be
the Erdős minimum overlap function: the least, over all pairs of disjoint finite sets
$A, B \subseteq \mathbb{Z}$ with $A \cup B = \{1, \dots, 2N\}$ and $|A| = |B|$, of the largest
number of pairs $(a, b) \in A \times B$ with a given difference $a - b$. Then $M(N)/N$ tends to
the continuous Erdős minimum-overlap constant $C_{1b}$ as $N \to \infty$.

Source: Haugland 2016 and Optimization Problems 1b. -/
public theorem_wanted continuousDiscreteEquivalence_holds : continuousDiscreteEquivalence

/-- **The continuous constant $C_{1b}$ is the largest asymptotic overlap constant.** Call a real
number $c$ a universal asymptotic lower bound when for every $\varepsilon > 0$ there is a
positive integer $N_0$ such that for every $N \ge N_0$ and all disjoint finite sets
$A, B \subseteq \mathbb{Z}$ with $A \cup B = \{1, \dots, 2N\}$ and $|A| = |B|$, some integer $x$
satisfies $(c - \varepsilon) N \le \#\{(a, b) \in A \times B : a - b = x\}$. Then the continuous
Erdős minimum-overlap constant $C_{1b}$ is a universal asymptotic lower bound, and every
universal asymptotic lower bound $c$ satisfies $c \le C_{1b}$.

Source: Haugland 2016 and the uniform partition clause of Optimization Problems 1b. -/
public theorem_wanted continuousDiscreteAsymptoticCharacterization_holds :
  continuousDiscreteAsymptoticCharacterization

/-- **Erdős's unpublished upper bound $4/9$ for the minimum-overlap constant.** The continuous
Erdős minimum-overlap constant $C_{1b}$ satisfies $C_{1b} \le 4/9$.

Source: Erdős, unpublished, recorded by Optimization Problems 1b. -/
public theorem_wanted upperBound_Erdos_unpublished_fourNinths_holds :
  upperBound_Erdos_unpublished_fourNinths

/-- **Motzkin–Ralston–Selfridge upper bound $5/12$ for the minimum-overlap constant.** The
continuous Erdős minimum-overlap constant $C_{1b}$ satisfies $C_{1b} \le 5/12$.

Source: Motzkin--Ralston--Selfridge 1956 and Optimization Problems 1b. -/
public theorem_wanted upperBound_MRS1956_fiveTwelfths_holds : upperBound_MRS1956_fiveTwelfths

/-- **Motzkin–Ralston–Selfridge upper bound $0.4$ for the minimum-overlap constant.** The
continuous Erdős minimum-overlap constant $C_{1b}$ satisfies $C_{1b} \le 0.4$.

Source: Motzkin--Ralston--Selfridge 1956 and Optimization Problems 1b. -/
public theorem_wanted upperBound_MRS1956_pointFour_holds : upperBound_MRS1956_pointFour

/-- **Haugland's unpublished 1993 upper bound for the minimum-overlap constant.** The continuous
Erdős minimum-overlap constant $C_{1b}$ satisfies $C_{1b} \le 0.385694$.

Source: Haugland, unpublished 1993, recorded by Optimization Problems 1b. -/
public theorem_wanted upperBound_Haugland_unpublished_1993_holds :
  upperBound_Haugland_unpublished_1993

/-- **Haugland's 1996 upper bound for the minimum-overlap constant.** The continuous Erdős
minimum-overlap constant $C_{1b}$ satisfies $C_{1b} \le 0.382002$.

Source: Haugland 1996 and Optimization Problems 1b. -/
public theorem_wanted upperBound_H1996_holds : upperBound_H1996

/-- **Haugland's 2016 upper bound for the minimum-overlap constant.** The continuous Erdős
minimum-overlap constant $C_{1b}$ satisfies $C_{1b} \le 0.380926$.

Source: Haugland 2016 and Optimization Problems 1b. -/
public theorem_wanted upperBound_H2016_holds : upperBound_H2016

/-- **AlphaEvolve upper bound for the minimum-overlap constant.** The continuous Erdős
minimum-overlap constant $C_{1b}$ satisfies $C_{1b} \le 0.380924$.

Source: Georgiev--Gómez-Serrano--Tao--Wagner 2025 and Optimization Problems 1b. -/
public theorem_wanted upperBound_GGSWT2025_AlphaEvolve_holds :
  upperBound_GGSWT2025_AlphaEvolve

/-- **TTT-Discover 2026 upper bound for the minimum overlap constant holds.** The continuous
Erdős minimum-overlap constant $C_{1b}$ is at most $0.380876$.

Source: Yuksekgonul et al. 2026 and Optimization Problems 1b. -/
public theorem_wanted upperBound_YKLBMWKCZGS2026_TTTDiscover_holds :
  upperBound_YKLBMWKCZGS2026_TTTDiscover

/-- **Together AI's 2026 upper bound for the minimum-overlap constant.** The continuous Erdős
minimum-overlap constant $C_{1b}$ satisfies $C_{1b} \le 0.380871$.

Source: Together AI 2026 and Optimization Problems 1b. -/
public theorem_wanted upperBound_T2026_TogetherAI_holds : upperBound_T2026_TogetherAI

/-- **SimpleTES 2026 upper bound for the minimum overlap constant holds.** The continuous
Erdős minimum-overlap constant $C_{1b}$ is at most $0.380868$.

Source: Ye et al. 2026 and Optimization Problems 1b. -/
public theorem_wanted upperBound_YLTLYSTYLLGDHZSWZSHMELCZX2026_SimpleTES_holds :
  upperBound_YLTLYSTYLLGDHZSWZSHMELCZX2026_SimpleTES

/-- **Erdős's lower bound $C_{1b} \ge 1/4$.** The continuous Erdős minimum-overlap constant
$C_{1b}$ satisfies $1/4 \le C_{1b}$.

Source: Erdős 1955 and Optimization Problems 1b. -/
public theorem_wanted lowerBound_E1955_quarter_holds : lowerBound_E1955_quarter

/-- **Scherk's lower bound for the minimum-overlap constant.** The continuous Erdős
minimum-overlap constant $C_{1b}$ satisfies $1 - 1/\sqrt{2} \le C_{1b}$.

Source: Scherk, unpublished 1955, recorded by Optimization Problems 1b. -/
public theorem_wanted lowerBound_Scherk_unpublished_1955_holds :
  lowerBound_Scherk_unpublished_1955

/-- **Świerczkowski's lower bound $C_{1b} \ge (4 - \sqrt{6})/5$.** The continuous Erdős
minimum-overlap constant $C_{1b}$ satisfies $(4 - \sqrt{6})/5 \le C_{1b}$.

Source: Swierczkowski 1958 and Optimization Problems 1b. -/
public theorem_wanted lowerBound_S1958_holds : lowerBound_S1958

/-- **Moser's lower bound $C_{1b} \ge \sqrt{4 - \sqrt{15}}$.** The continuous Erdős minimum-overlap
constant $C_{1b}$ satisfies $\sqrt{4 - \sqrt{15}} \le C_{1b}$.

Source: Moser 1959 and Optimization Problems 1b. -/
public theorem_wanted lowerBound_M1959_holds : lowerBound_M1959

/-- **White's lower bound for the minimum-overlap constant.** The continuous Erdős minimum-overlap
constant $C_{1b}$ satisfies $0.379005 \le C_{1b}$.

Source: White 2022 and Optimization Problems 1b. -/
public theorem_wanted lowerBound_W2022_holds : lowerBound_W2022

end MathlibExt.NumberTheory.ErdosMinimumOverlapConstantWanted
