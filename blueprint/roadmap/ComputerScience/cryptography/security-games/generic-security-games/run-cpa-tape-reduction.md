# Running the fixed-tape CPA distinguisher

For every keyed function $O \colon Q \to A$, every oracle encryption algorithm $\mathrm{encQ}$, every CPA adversary, every budget $q$ and every fixed coin tuple $(b, r, \rho, r_s)$, running the [reduction](cpa-tape-reduction.md) against $O$ returns

$$
\bigl[\mathrm{guess}(e, A.\mathrm{run}(r), q, \rho, r_s, b) = b\bigr], \qquad e(m, u) = \mathrm{encQ}(m, u).\mathrm{run}(O),
$$

where $\mathrm{guess}$ is the [fixed-tape guess](cpa-tape-guess.md): the two stages share the $q$ entries of $\rho$, the challenge uses $r_s$, and a query beyond the tape makes the guess `false`. This is a pointwise equation; it needs no finiteness, uniform-coin or query-bound hypothesis.
