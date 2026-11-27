# Weak initiality of the fully abstract model of PCF

A *general interpretation* of [PCF with the parallel conditional](pcf-with-the-parallel-conditional.md) assigns a cpo $D_\sigma$ to each type, continuous application maps
$\mathrm{Ap}_{\sigma\tau} : D_{\sigma \to \tau} \times D_\sigma \to D_\tau$ and a denotation $[\![M]\!](\rho) \in D_\sigma$ to each term $M : \sigma$ in each type-respecting environment $\rho$, such that a variable denotes $\rho(x)$, an
application denotes $[\![M\, N]\!](\rho) = \mathrm{Ap}([\![M]\!](\rho), [\![N]\!](\rho))$, and a closed term denotes independently of $\rho$; denotations of open terms are ordered
pointwise in $\rho$. It is *fully abstract* if $M \sqsubseteq N$ operationally (in every program context) exactly when $[\![M]\!] \sqsubseteq [\![N]\!]$. A *morphism* of general interpretations
is a family of continuous maps $\Phi_\sigma$ commuting with application, sending the denotation of a closed term below its denotation in the target, and preserving the
denotations of programs. For the standard model, which is [fully abstract](full-abstraction-of-pcf-with-the-parallel.md):

1. for every fully abstract general interpretation $\mathcal{B}$ there is a monomorphism from the standard model into $\mathcal{B}$, defined by sending $x$ to the join of the
   denotations in $\mathcal{B}$ of the closed terms whose denotations are finite and below $x$;
2. if a fully abstract general interpretation also has this property, it is isomorphic to the standard model, by a unique isomorphism.

So the standard model is a weakly initial fully abstract model; products of fully abstract interpretations are again fully abstract, so it is not the only one.

## Depends on

- [Full abstraction of PCF with the parallel conditional](full-abstraction-of-pcf-with-the-parallel.md)
- [PCF with the parallel conditional](pcf-with-the-parallel-conditional.md)

## Proof depends on

- [Finite elements are definable in PCF with the parallel conditional](finite-elements-are-definable-with-parallel.md)
- [Full abstraction of PCF with the parallel conditional](full-abstraction-of-pcf-with-the-parallel.md)

## Sources

- G. D. Plotkin, "LCF considered as a programming language", *Theoretical Computer Science* 5(3):223–255, 1977, <https://homepages.inf.ed.ac.uk/gdp/publications/LCF.pdf>: Section 4, the definitions of general interpretation, fully abstract general interpretation and morphism, and Theorem 4.6 with its proof.
