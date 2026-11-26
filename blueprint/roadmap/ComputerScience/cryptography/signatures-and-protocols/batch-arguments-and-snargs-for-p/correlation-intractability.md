# Correlation-intractable hash families

A keyed hash family $\{h_k:\{0,1\}^{n}\to\{0,1\}^{m}\}$ is *correlation intractable* for a relation $R\subseteq\{0,1\}^{n}\times\{0,1\}^{m}$ if for every efficient adversary, $\Pr_k[\mathcal{A}(k)\to x\text{ with }(x,h_k(x))\in R]$ is negligible. It is correlation intractable for *efficiently searchable* relations if this holds for every sparse relation $R$ for which, given $x$, the unique $y$ with $(x,y)\in R$ (if any) is computable by a circuit of fixed polynomial size. Correlation intractability for the bad-challenge relation of a public-coin interactive proof makes the Fiat–Shamir transform sound for it in the standard model.

## Depends on

- [Security of the Fiat–Shamir transform](../zero-knowledge-and-arguments/security-of-the-fiatshamir-transform.md)

## Sources

- Ran Canetti, Yilei Chen, Justin Holmgren, Alex Lombardi, Guy N. Rothblum, Ron D. Rothblum, Daniel Wichs, "Fiat-Shamir: From Practice to Theory", STOC (2019).
- Chris Peikert, Sina Shiehian, "Noninteractive Zero Knowledge for NP from (Plain) Learning With Errors", CRYPTO (2019).
