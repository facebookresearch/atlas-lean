/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Exact linear counting for Höhn–Seysen, arXiv:2508.01037v1 (1 August 2025),
Table 4 and §4. The matrix and count vector below transcribe mathematical
statements of that source. The rational inverse certificate was independently
computed by Gaussian elimination and is checked by Lean's kernel.

Application to the actual feasible-axis orbit still requires the transition
equations and anchored orbit calculation; those inputs are explicit below.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TransitionCountSystem

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Matrix

/-- Table 4, with rows and columns ordered as Table 3. -/
def feasibleAxisTransitionMatrix : Matrix (Fin 10) (Fin 10) ℚ :=
![
  ![
    0,
    1,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0],
  ![
    93150,
    925,
    63,
    15,
    1,
    0,
    0,
    0,
    0,
    0],
  ![
    0,
    4928,
    63,
    120,
    42,
    1,
    0,
    0,
    0,
    0],
  ![
    0,
    42240,
    4320,
    1815,
    420,
    30,
    15,
    0,
    0,
    0],
  ![
    0,
    45056,
    24192,
    6720,
    1807,
    272,
    120,
    891,
    27,
    0],
  ![
    0,
    0,
    64512,
    53760,
    30464,
    10287,
    5040,
    24948,
    3060,
    3850],
  ![
    0,
    0,
    0,
    30720,
    15360,
    5760,
    3495,
    0,
    4320,
    4125],
  ![
    0,
    0,
    0,
    0,
    2048,
    512,
    0,
    891,
    36,
    100],
  ![
    0,
    0,
    0,
    0,
    43008,
    43520,
    53760,
    24948,
    53451,
    53900],
  ![
    0,
    0,
    0,
    0,
    0,
    32768,
    30720,
    41472,
    32256,
    31175]]

/-- The ten feasible-axis counts in Table 3. -/
def feasibleAxisCountVector : Fin 10 → ℚ :=
  ![1, 93150, 7286400, 262310400, 4196966400, 470060236800,
    537211699200, 9646899200, 6685301145600, 4000762036224]

/-- An independently computed inverse for the anchored transition system. -/
def feasibleAxisTransitionInverse : Matrix (Fin 10) (Fin 10) ℚ :=
![
  ![
    1,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0],
  ![
    93150,
    -1,
    -1,
    -1,
    -1,
    -1,
    -1,
    -1,
    -1,
    -1],
  ![
    7286400,
    (-704 : ℚ) / 9,
    (-3850623124525646491871 : ℚ) / 49226176221877634625,
    (-770124523617446529304 : ℚ) / 9845235244375526925,
    (-132780090484341684338 : ℚ) / 1697454352478539125,
    (-26954358370124321646823 : ℚ) / 344583233553143442375,
    (-256708174953292857512 : ℚ) / 3281745081458508975,
    (-47538550917270926686 : ℚ) / 607730570640464625,
    (-5390871674020807200202 : ℚ) / 68916646710628688475,
    (-154024904972027007134 : ℚ) / 1969047048875105385],
  ![
    262310400,
    -2816,
    (-3080498094469786117216 : ℚ) / 1093915027152836325,
    (-3080498123302718206963 : ℚ) / 1093915027152836325,
    (-106224072983421188068 : ℚ) / 37721207832856425,
    (-21563486818063288973738 : ℚ) / 7657405190069854275,
    (-38030840948961648699 : ℚ) / 13505123792010325,
    (-38030840948915589996 : ℚ) / 13505123792010325,
    (-862539472722252623476 : ℚ) / 306296207602794171,
    (-123219924674611676389 : ℚ) / 43756601086113453],
  ![
    4196966400,
    -45056,
    (-8497925790997867797632 : ℚ) / 188606039164282125,
    (-1699585167734739009088 : ℚ) / 37721207832856425,
    (-8497925854778938082659 : ℚ) / 188606039164282125,
    (-59485480976736021655216 : ℚ) / 1320242274149974875,
    (-566528390254744562024 : ℚ) / 12573735944285475,
    (-104912664862110185487 : ℚ) / 2328469619312125,
    (-11897096195351790562309 : ℚ) / 264048454829994975,
    (-339917034152896594328 : ℚ) / 7544241566571285],
  ![
    470060236800,
    -5046272,
    (-27601262971007305366346752 : ℚ) / 5469575135764181625,
    (-5520252625424201977276928 : ℚ) / 1093915027152836325,
    (-951767695627776346483456 : ℚ) / 188606039164282125,
    (-193208842237810089823458401 : ℚ) / 38287025950349271375,
    (-1840084211785723681113424 : ℚ) / 364638342384278775,
    (-340756335515698500384532 : ℚ) / 67525618960051625,
    (-38641768447515305854501724 : ℚ) / 7657405190069854275,
    (-1104050527071918441580138 : ℚ) / 218783005430567265],
  ![
    537211699200,
    -5767168,
    (-2102953369217375088738304 : ℚ) / 364638342384278775,
    (-77887162263473456535552 : ℚ) / 13505123792010325,
    (-72515633952607303939072 : ℚ) / 12573735944285475,
    (-14720673694285789448907392 : ℚ) / 2552468396689951425,
    (-2102953384903182484000577 : ℚ) / 364638342384278775,
    (-77887162403592098202752 : ℚ) / 13505123792010325,
    (-2944134738860315828199392 : ℚ) / 510493679337990285,
    (-84118135396011081884131 : ℚ) / 14585533695371151],
  ![
    9646899200,
    (-8388608 : ℚ) / 81,
    (-6230972945828534902587392 : ℚ) / 60165326493405997875,
    (-138466066246007339220992 : ℚ) / 1337007255409022175,
    (-6510943564775807875072 : ℚ) / 62868679721427375,
    (-6230972992287058292745728 : ℚ) / 60165326493405997875,
    (-1246194598457473571244032 : ℚ) / 12033065298681199575,
    (-76925592505359335030897 : ℚ) / 742781808560567875,
    (-113290418041641368130452 : ℚ) / 1093915027152836325,
    (-9231071099690252957924 : ℚ) / 89133817027268145],
  ![
    6685301145600,
    (-645922816 : ℚ) / 9,
    (-706592332057255241344876544 : ℚ) / 9845235244375526925,
    (-28263693442162773966061568 : ℚ) / 393809409775021077,
    (-24365253008080467071608832 : ℚ) / 339490870495707825,
    (-4946146361281959149376220672 : ℚ) / 68916646710628688475,
    (-47106155821765053251190272 : ℚ) / 656349016291701795,
    (-8723362189206385346044804 : ℚ) / 121546114128092925,
    (-989229272257649366706093973 : ℚ) / 13783329342125737695,
    (-28263693493072279171641404 : ℚ) / 393809409775021077],
  ![
    4000762036224,
    (-1073741824 : ℚ) / 25,
    (-2584109100095171056520658944 : ℚ) / 60165326493405997875,
    (-516821822942422452725088256 : ℚ) / 12033065298681199575,
    (-8100655545543356802138112 : ℚ) / 188606039164282125,
    (-2584109119363758820978425856 : ℚ) / 60165326493405997875,
    (-172273941291030695698700288 : ℚ) / 4011021766227066525,
    (-31902581720529514222585344 : ℚ) / 742781808560567875,
    (-46983802170301970571040256 : ℚ) / 1093915027152836325,
    (-103364364774692790258439181 : ℚ) / 2406613059736239915]]

set_option maxHeartbeats 0 in
-- The closed rational matrix check exceeds the default reduction budget.
set_option maxRecDepth 10000 in
/-- The explicit rational certificate is a genuine left inverse. -/
theorem feasibleAxisTransition_left_inverse :
    feasibleAxisTransitionInverse *
      transitionCountSystem feasibleAxisTransitionMatrix 93150 = 1 := by
  decide +kernel

set_option maxHeartbeats 0 in
-- The closed rational matrix check exceeds the default reduction budget.
set_option maxRecDepth 10000 in
/-- Kernel-checked balance for the source count vector. -/
theorem feasibleAxisCountVector_balance :
    feasibleAxisTransitionMatrix *ᵥ feasibleAxisCountVector =
      (93150 : ℚ) • feasibleAxisCountVector := by
  decide +kernel

/-- The ten transition equations and the orbit of size one determine every
count uniquely. -/
theorem feasible_axis_counts_of_transition
    (v : Fin 10 → ℚ)
    (hbalance : feasibleAxisTransitionMatrix *ᵥ v = (93150 : ℚ) • v)
    (hanchor : v 0 = 1) : v = feasibleAxisCountVector :=
  transition_count_unique feasibleAxisTransitionMatrix feasibleAxisTransitionInverse
    93150 feasibleAxisTransition_left_inverse v feasibleAxisCountVector hbalance
    feasibleAxisCountVector_balance hanchor

set_option maxHeartbeats 0 in
-- The closed rational sum exceeds the default reduction budget.
/-- The total of the feasible-axis vector, checked in rational arithmetic. -/
theorem feasibleAxisCountVector_sum :
    (∑ i, feasibleAxisCountVector i) = 11707448673375 := by
  decide +kernel

/-- The anchored transition calculation determines the total as well. -/
theorem feasible_axis_count_sum_of_transition
    (v : Fin 10 → ℚ)
    (hbalance : feasibleAxisTransitionMatrix *ᵥ v = (93150 : ℚ) • v)
    (hanchor : v 0 = 1) : (∑ i, v i) = 11707448673375 := by
  rw [feasible_axis_counts_of_transition v hbalance hanchor]
  exact feasibleAxisCountVector_sum

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
