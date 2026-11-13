# Solution of Erdős Problem 369, location variant

For every real $\varepsilon > 0$ and every
natural number $k \ge 2$ there is a natural number $N$ such that for every natural number
$n \ge N$ there is a natural number $a$ with $\lfloor n/2 \rfloor \le a + 1$ and $a + k \le n$
for which every prime factor $p$ of each of the $k$ consecutive integers $a + 1, \dots, a + k$
satisfies $p \le n^\varepsilon$.

## Sources

- Balog-Wooley 1998; Bober-Fretwell-Martin-Wooley 2020.
- Lean proof of EP-369 location variant (plby/lean-proofs), https://github.com/plby/lean-proofs/blob/1d7b3f00780b85ed0462e79a1cd5650ee9055655/src/v4.29.1/ErdosProblems/Erdos369.lean.
