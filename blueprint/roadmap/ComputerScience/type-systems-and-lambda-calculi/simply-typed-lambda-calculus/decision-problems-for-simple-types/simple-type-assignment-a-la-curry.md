# Simple type assignment à la Curry

Simple types are built from type variables $\alpha, \beta, \dots$ by $\sigma \to \tau$. A context $\Gamma$ is a finite set of declarations $x : \sigma$ of distinct
variables. Simple type assignment derives judgments $\Gamma \vdash M : \tau$ for *pure* (untyped) λ-terms $M$ by

- $\Gamma, x : \tau \vdash x : \tau$;
- if $\Gamma, x : \sigma \vdash M : \tau$ then $\Gamma \vdash \lambda x.\, M : \sigma \to \tau$;
- if $\Gamma \vdash M : \sigma \to \tau$ and $\Gamma \vdash N : \sigma$ then $\Gamma \vdash M\, N : \tau$.

For this system:

- *type checking* asks, given $\Gamma$, $M$ and $\tau$, whether $\Gamma \vdash M : \tau$;
- *type reconstruction* (typability) asks, given $M$, whether $\Gamma \vdash M : \tau$ for some $\Gamma$ and $\tau$;
- *inhabitation* asks, given $\tau$, whether $\vdash M : \tau$ for some closed term $M$.

A pair $(\Gamma, \tau)$ with $\Gamma \vdash M : \tau$ is *principal* for $M$ if every pair $(\Gamma', \tau')$ with $\Gamma' \vdash M : \tau'$, $\Gamma'$ declaring exactly the free variables
of $M$, is obtained from it by a substitution of types for type variables.

## Depends on

- [Named, de Bruijn and locally nameless lambda terms](../../syntax-with-binders/named-de-bruijn-and-locally-nameless-lambda-terms.md)
- [Simple types](../ty.md)

## Sources

- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Definitions 3.1.1–3.1.3 (simply typed λ-calculus à la Curry), Definition 6.0.11 (type checking, type reconstruction and inhabitation) and Definition 6.4.4 (principal pairs).
