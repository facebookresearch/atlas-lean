# Delimited release

Let $c$ be a program containing declassification expressions $\mathrm{declassify}(e_1), \dots, \mathrm{declassify}(e_k)$ (escape hatches) and $=_L$ low equivalence of stores. The program satisfies *delimited release* if for all initial stores $\sigma_1 =_L \sigma_2$ such that $\llbracket e_i \rrbracket \sigma_1 = \llbracket e_i \rrbracket \sigma_2$ for every $i$, whenever $c$ terminates from both, the final stores are low equivalent.

The escape hatches form the policy: the definition bounds what may be released, but does not require that the information actually flows
through the declassify expressions. For example, $\mathbf{if}\ \mathrm{true}\ \mathbf{then}\ l := h * h\ \mathbf{else}\ l := \mathrm{declassify}(h * h)$ satisfies
delimited release. Type systems that enforce delimited release, and its relation to the dimensions and principles of declassification, are
separate pages.

## Depends on

- [Security levels, policies and low equivalence](security-levels-policies-and-low-equivalence.md)

## Sources

- A. Sabelfeld and D. Sands, "Declassification: dimensions and principles", *Journal of Computer Security* 17(5):517–548, 2009, <https://www.cse.chalmers.se/~andrei/sabelfeld-sands-jcs07.pdf>: Section 2.1, "What", paragraph "Delimited release" (the definition and the example).
