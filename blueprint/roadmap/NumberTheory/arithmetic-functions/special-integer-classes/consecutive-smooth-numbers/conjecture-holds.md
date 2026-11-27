# Solution of Erdős Problem 369, location variant

For every real $\varepsilon > 0$ and every
natural number $k \ge 2$ there is a natural number $N$ such that for every natural number
$n \ge N$ there is a natural number $a$ with $\lfloor n/2 \rfloor \le a + 1$ and $a + k \le n$
for which every prime factor $p$ of each of the $k$ consecutive integers $a + 1, \dots, a + k$
satisfies $p \le n^\varepsilon$.

## Sources

- Erdős Problem #369, https://www.erdosproblems.com/369, which discusses this variant and an adaptation of the Balog–Wooley construction.
- A. Balog and T. D. Wooley, *On strings of consecutive integers with no large prime factors*, J. Austral. Math. Soc. Ser. A 64 (1998), 266–276.
- J. W. Bober, D. Fretwell, G. Martin and T. D. Wooley, *Smooth values of polynomials*, J. Aust. Math. Soc. 108 (2020), 245–261, doi:10.1017/S1446788718000320.
- plby/lean-proofs, `ErdosProblems/Erdos369.lean`, https://github.com/plby/lean-proofs/blob/1d7b3f00780b85ed0462e79a1cd5650ee9055655/src/v4.29.1/ErdosProblems/Erdos369.lean.
