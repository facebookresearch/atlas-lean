# Union bound for centered-binomial polynomial noise

Let $\mathbf{x} \in R_q^k$ have independent coefficients from $\mathrm{CBD}_\eta$, reduced modulo $q$, with $2\eta < q$. For every radius $t \ge 0$,

$$
\Pr\bigl[\exists\, i, j:\ |\mathrm{centered}(x_{i,j})| > t\bigr] \;\le\; k n \cdot \Pr_{X \sim \mathrm{CBD}_\eta}\bigl[|X| > t\bigr] \;\le\; 2 k n\, e^{-t^2/\eta},
$$

where the strict no-wrap condition $2\eta < q$ guarantees that the centered lift of each coefficient equals the sampled integer, so in particular $\|\mathbf{x}\|_\infty \le \eta$ always.

## Proof sketch

Apply the union bound over the $kn$ coefficients and Hoeffding's inequality to the sum of $2\eta$ independent $\pm\frac12$-centered bits.

## Depends on

- [The centered binomial distribution](centered-binomial-distribution.md)

## Sources

- Roberto Avanzi et al., "CRYSTALS-Kyber: Algorithm Specifications and Supporting Documentation (version 3.02)", Third-round submission to the NIST post-quantum cryptography standardization process, dated 4 August 2021.
