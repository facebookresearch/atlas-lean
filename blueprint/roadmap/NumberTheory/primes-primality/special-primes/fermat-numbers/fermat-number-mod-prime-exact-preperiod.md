# Preperiod and period of Fermat numbers modulo an odd prime

Let $p$ be an odd prime
and write the multiplicative order of $2$ modulo $p$ as $2^v w$ with $v, w$ natural numbers and
$w$ odd. Let $k$ be the multiplicative order of $2$ modulo $w$ (so $k = 1$ when $w = 1$), and
let $F_m = 2^{2^m} + 1$ be the $m$-th Fermat number. Then the sequence $n \mapsto F_{v+n} \bmod p$
is periodic with period $k$; for every $h < v$, the sequence $n \mapsto F_{h+n} \bmod p$ has no
positive period; and every positive period of the sequence $n \mapsto F_{v+n} \bmod p$ is
divisible by $k$.

## Sources

- `https://cs.uwaterloo.ca/journals/JIS/VOL28/Klaska/klaska22.tex`, Theorem `thm:5`, lines 593--606 of `56ede62e8bb2abc2c9097317bce881d696be23082f48fa2822d297f0f11e65af.tex` (source SHA-256 `56ede62e8bb2abc2c9097317bce881d696be23082f48fa2822d297f0f11e65af`, excerpt SHA-256 `e4893c51946a5353f9ac51df8a431d7a4374170b122bfcb5befb12ae3d342bd7`). Concept `jis_dep_f3be3eca42e403215ccd3864` (grounded `jis_grounded_b5fc700e81e8282d5e992c5d`); accounting: 7 mentions / 3 papers / 2 proof uses. This is the complete selected theorem statement, not a prerequisite stage. Proves `Wanted` entry `fermatNumber_mod_prime_exact_preperiod_period`.
