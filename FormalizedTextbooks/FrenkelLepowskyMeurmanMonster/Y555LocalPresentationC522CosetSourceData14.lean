/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact literal source equations and their independently proved source-family labels. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC522CosetSourceFamilies
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationRawCosetPrograms

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Exact packed signed source word pairs in this bounded source interval. -/
def y522CosetSourceRaw14 : Fin 71 → List ℕ × List ℕ :=
  ![
    ([3471], [3469, 13]),
    ([3473], [2867, 17]),
    ([3475], [3473, 1]),
    ([3477], [3475, 3]),
    ([3479], [3477, 5]),
    ([3481], [3479, 11]),
    ([3483], [3481, 1]),
    ([3485], [3483, 15]),
    ([3487], [1527, 7]),
    ([3489], [3487, 15]),
    ([3491], [3489, 7]),
    ([3493], [1587, 3]),
    ([3495], [1337, 7]),
    ([3497], [3375, 1]),
    ([3499], [2067, 7]),
    ([3501], [3499, 11]),
    ([3503], [3501, 7]),
    ([3505], [2083, 3]),
    ([3507], [2045, 7]),
    ([3509], [3389, 1]),
    ([3511], [2021, 7]),
    ([3513], [2021, 11]),
    ([3515], [2043, 7]),
    ([3517], [2043, 11]),
    ([3519], [811, 9]),
    ([3521], [813, 9]),
    ([3523], [771, 9]),
    ([3525], [2255, 9]),
    ([3527], [3525, 7]),
    ([3529], [3527, 9]),
    ([3531], [563, 9]),
    ([3533], [2229, 9]),
    ([3535], [3533, 7]),
    ([3537], [3535, 9]),
    ([3539], [3119, 15]),
    ([3541], [565, 9]),
    ([3543], [973, 9]),
    ([3545], [2489, 9]),
    ([3547], [3545, 7]),
    ([3549], [3547, 9]),
    ([3551], [567, 9]),
    ([3553], [2285, 9]),
    ([3555], [3553, 7]),
    ([3557], [3555, 9]),
    ([3559], [941, 9]),
    ([3561], [1965, 9]),
    ([3563], [3561, 7]),
    ([3565], [3563, 9]),
    ([3567], [1007, 9]),
    ([3569], [2339, 9]),
    ([3571], [3569, 7]),
    ([3573], [3571, 9]),
    ([3575], [819, 9]),
    ([3577], [949, 9]),
    ([3579], [2033, 9]),
    ([3581], [3579, 7]),
    ([3583], [3581, 9]),
    ([3585], [2035, 9]),
    ([3587], [3585, 7]),
    ([3589], [3587, 9]),
    ([3591], [3191, 15]),
    ([3593], [1649, 9]),
    ([3595], [3593, 7]),
    ([3597], [3595, 9]),
    ([3599], [1147, 9]),
    ([3601], [1619, 9]),
    ([3603], [3601, 7]),
    ([3605], [3603, 9]),
    ([3607], [2381, 9]),
    ([3609], [3607, 7]),
    ([3611], [3609, 9])]

/-- Exact original-source family of each literal source equation in this interval. -/
def y522CosetSourceKind14 : Fin 71 → Y522CosetSourceKind :=
  ![
    .path 1724,
    .path 1725,
    .path 1726,
    .path 1727,
    .path 1728,
    .path 1729,
    .path 1730,
    .path 1731,
    .path 1732,
    .path 1733,
    .path 1734,
    .path 1735,
    .path 1736,
    .path 1737,
    .path 1738,
    .path 1739,
    .path 1740,
    .path 1741,
    .path 1742,
    .path 1743,
    .path 1744,
    .path 1745,
    .path 1746,
    .path 1747,
    .path 1748,
    .path 1749,
    .path 1750,
    .path 1751,
    .path 1752,
    .path 1753,
    .path 1754,
    .path 1755,
    .path 1756,
    .path 1757,
    .path 1758,
    .path 1759,
    .path 1760,
    .path 1761,
    .path 1762,
    .path 1763,
    .path 1764,
    .path 1765,
    .path 1766,
    .path 1767,
    .path 1768,
    .path 1769,
    .path 1770,
    .path 1771,
    .path 1772,
    .path 1773,
    .path 1774,
    .path 1775,
    .path 1776,
    .path 1777,
    .path 1778,
    .path 1779,
    .path 1780,
    .path 1781,
    .path 1782,
    .path 1783,
    .path 1784,
    .path 1785,
    .path 1786,
    .path 1787,
    .path 1788,
    .path 1789,
    .path 1790,
    .path 1791,
    .path 1792,
    .path 1793,
    .path 1794]

set_option maxRecDepth 100000 in
-- Exact signed-letter bounds are checked for at most 128 literal source pairs.
/-- Both literal source sides belong to the exact actual finite symbol alphabet. -/
theorem y522CosetSourceRaw14_allowed (i : Fin 71) :
    y322RawEquationWordAllowed 1806 (y522CosetSourceRaw14 i).1 ∧
      y322RawEquationWordAllowed 1806 (y522CosetSourceRaw14 i).2 := by
  revert i
  decide +kernel

/-- Exact decoded source equation, preserving every bound-checked signed letter. -/
def y522CosetSourceEquation14 (i : Fin 71) : Y322WordEquation (Fin 1806) :=
  ⟨y322RawEquationWordDecode 1806 (y522CosetSourceRaw14 i).1
      (y522CosetSourceRaw14_allowed i).1,
    y322RawEquationWordDecode 1806 (y522CosetSourceRaw14 i).2
      (y522CosetSourceRaw14_allowed i).2⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
