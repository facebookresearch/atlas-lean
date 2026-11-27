# Log-concavity of the independent set numbers of a matroid

For every finite matroid $M$ and every $k \ge 1$,

$$f_{k-1}(M) \, f_{k+1}(M) \le f_k(M)^2,$$

where $f_k(M)$ is the number of independent sets of $M$ with $k$ elements.

This is the conjecture of Welsh and Mason (Conjecture 1.2 of Adiprasito, Huh and Katz), proved
as their Theorem 9.9 (3). They state it for $1 \le k \le r$, where $r + 1$ is the rank; for
larger $k$ the left-hand side vanishes. Lenz had deduced it for matroids realizable over some
field from the Huh–Katz theorem. The ultra log-concave strengthening is the
[strong Mason conjecture](strong-mason-conjecture.md), which implies this statement because
$\binom{n}{k}^2 \ge \binom{n}{k-1}\binom{n}{k+1}$.

## Informally uses

- [Log-concavity of the reduced characteristic polynomial](../heron-rota-welsh-conjecture/reduced-char-poly-coeff-log-concave.md):
  by a result of Brylawski, $f_k(M)$ is the absolute value of a coefficient of the reduced
  characteristic polynomial of another matroid, and Theorem 9.9 (1) applies to that matroid.

## Sources

- K. Adiprasito, J. Huh and E. Katz, *Hodge theory for combinatorial geometries*, Ann. of
  Math. 188 (2018), 381–452, Conjecture 1.2 and Theorem 9.9 (3),
  https://arxiv.org/abs/1511.02888.
