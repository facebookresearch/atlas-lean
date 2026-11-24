# Delimited release

Let $c$ be a program containing declassification expressions $\mathrm{declassify}(e_1), \dots, \mathrm{declassify}(e_k)$ (escape hatches) and $=_L$ low equivalence of stores. The program satisfies *delimited release* if for all initial stores $\sigma_1 =_L \sigma_2$ such that $\llbracket e_i \rrbracket \sigma_1 = \llbracket e_i \rrbracket \sigma_2$ for every $i$, whenever $c$ terminates from both, the final stores are low equivalent.

## Depends on

- [Security levels, policies and low equivalence](security-levels-policies-and-low-equivalence.md)

## Sources

- A. Sabelfeld and A. C. Myers, "A model for delimited information release", *ISSS 2003*, LNCS 3233, Springer, 2004
- A. Sabelfeld and D. Sands, "Declassification: dimensions and principles", *Journal of Computer Security* 17(5):517–548, 2009
