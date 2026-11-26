# Two-cycles of elliptic curves for recursive arguments

A *2-cycle of elliptic curves* is a pair of elliptic curves $(E_1,E_2)$ such that the scalar field of $E_1$ equals the base field of $E_2$ and the scalar field of $E_2$ equals the base field of $E_1$. For prime-order groups this means $E_1/\mathbb{F}_p$ and $E_2/\mathbb{F}_q$ with $p\ne q$ prime, $\#E_1(\mathbb{F}_p)=q$ and $\#E_2(\mathbb{F}_q)=p$. Thus a constraint system over $\mathbb{F}_q$, the scalar field of $E_1$, can perform group operations on $E_2$ without emulating another field, and vice versa. In the instantiation of folding-based recursion on such a cycle used for Nova, an instance over the scalar field of one curve is folded by a verifier circuit over the scalar field of the other, so the folding verifier is represented as a circuit on both curves.

## Sources

- Abhiram Kothapalli, Srinath Setty, "HyperNova: Recursive Arguments for Customizable Constraint Systems", CRYPTO (2024), IACR ePrint 2023/573, Section 1 (footnote defining 2-cycles) and Section 8.1.
- Wilson Nguyen, Dan Boneh, Srinath Setty, "Revisiting the Nova Proof System on a Cycle of Curves", AFT (2023).
