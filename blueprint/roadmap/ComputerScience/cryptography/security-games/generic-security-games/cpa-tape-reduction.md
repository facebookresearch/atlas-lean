# Distinguisher from a CPA adversary on a fixed tape

Let $\mathrm{encQ}(m, u)$ be an oracle computation that encrypts the message $m$ with randomness $u$ by querying a keyed function $Q \to A$ (for instance a PRF or a block cipher). From a CPA adversary and a query budget $q$, the reduction is the oracle computation for that keyed function which, on its own coins $(b, r, \rho, r_s)$ with $\rho$ a tape of $q$ entries, does the following:

- it runs the first stage of the adversary on coins $r$, answering the $i$th encryption query $m$ by running $\mathrm{encQ}(m, \rho_i)$;
- when the first stage returns messages $(m_0, m_1)$ and a second stage, it computes the challenge by running $\mathrm{encQ}(m_b, r_s)$ with the separate entry $r_s$, and runs the second stage on it, continuing with the tape entries the first stage left unused;
- if either stage asks a query when no tape entry is left, the adversary's guess is taken to be `false`;
- it outputs whether the guess equals $b$.

So an overflowing adversary makes the guess `false`, not the output; the output is then true exactly when $b$ is false.
