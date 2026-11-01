/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Literal acyclic path parents and exact source-generator bounds in this finite interval. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Exact raw parent and generator indices, before any finite generator decoding. -/
def y422TPathRawData15 : Fin 128 → ℕ × ℕ :=
  ![(1919, 7),
    (1920, 8),
    (1921, 0),
    (1922, 1),
    (1923, 2),
    (1924, 0),
    (1925, 5),
    (1926, 6),
    (1927, 0),
    (1928, 7),
    (1929, 8),
    (1930, 0),
    (1931, 1),
    (1932, 2),
    (1933, 0),
    (1934, 5),
    (1935, 6),
    (1936, 0),
    (1937, 7),
    (1938, 8),
    (1939, 0),
    (1940, 1),
    (1941, 2),
    (1942, 0),
    (1943, 5),
    (1944, 6),
    (1945, 0),
    (1946, 7),
    (1947, 8),
    (1948, 0),
    (1949, 1),
    (1950, 2),
    (1951, 0),
    (1952, 5),
    (1953, 6),
    (1954, 0),
    (1955, 7),
    (1956, 8),
    (1957, 0),
    (1958, 1),
    (1959, 2),
    (1960, 0),
    (1961, 5),
    (1962, 6),
    (1894, 7),
    (1964, 0),
    (1965, 1),
    (1966, 2),
    (1967, 5),
    (1968, 6),
    (1969, 0),
    (1970, 7),
    (1971, 8),
    (1972, 1),
    (1973, 2),
    (1974, 0),
    (1975, 5),
    (1976, 6),
    (1977, 0),
    (1978, 7),
    (1979, 8),
    (1980, 0),
    (1981, 1),
    (1982, 2),
    (1983, 0),
    (1984, 5),
    (1985, 6),
    (1986, 0),
    (1987, 7),
    (1988, 8),
    (1989, 0),
    (1990, 1),
    (1991, 2),
    (1992, 0),
    (1993, 5),
    (1994, 6),
    (1995, 0),
    (1996, 7),
    (1997, 8),
    (1998, 0),
    (1999, 1),
    (2000, 2),
    (2001, 0),
    (2002, 5),
    (2003, 6),
    (2004, 0),
    (2005, 7),
    (2006, 8),
    (2007, 0),
    (2008, 1),
    (2009, 2),
    (2010, 0),
    (2011, 5),
    (2012, 6),
    (2013, 0),
    (2014, 7),
    (2015, 8),
    (2016, 0),
    (2017, 1),
    (2018, 2),
    (2019, 0),
    (2020, 5),
    (2021, 6),
    (2022, 0),
    (2023, 7),
    (2024, 8),
    (2025, 0),
    (2026, 1),
    (2027, 2),
    (2028, 0),
    (188, 8),
    (1692, 1),
    (2031, 2),
    (2032, 5),
    (2033, 6),
    (2034, 0),
    (2035, 7),
    (2036, 8),
    (2037, 1),
    (2038, 2),
    (2039, 0),
    (2040, 5),
    (2041, 6),
    (2042, 0),
    (2043, 7),
    (2044, 8),
    (2045, 0),
    (2046, 1)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData15_allowed (j : Fin 128) :
    (1920 + j.val = 0 ∨ (y422TPathRawData15 j).1 < 1920 + j.val) ∧
      (y422TPathRawData15 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
