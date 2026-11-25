# Elaboration of ML modules into F-omega

For a module language with structures, signatures with abstract and manifest type components, sealing and generative functors, Rossberg, Russo and Dreyer's elaboration translates modules into terms of System $F_\omega$ and signatures into semantic signatures, abstract types becoming existential quantifiers and functor parameters universal quantifiers. Elaboration is sound: if a module elaborates to an $F_\omega$ term $e$ with semantic signature $\Xi$, then $e$ has the $F_\omega$ type corresponding to $\Xi$.

## Expansion

This page becomes ready once:

- Source module language: syntax of structures, signatures, sealing and generative functors, well-formed contexts and the elaboration judgment (statement prerequisite; not yet stated)
- Typing of System F_ω (statement prerequisite; not yet stated)

## Sources

- A. Rossberg, C. V. Russo and D. Dreyer, "F-ing modules", *Journal of Functional Programming* 24(5):529–607, 2014
