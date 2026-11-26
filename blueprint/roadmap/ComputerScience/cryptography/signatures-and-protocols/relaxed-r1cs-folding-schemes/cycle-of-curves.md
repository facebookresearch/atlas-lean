# Two-cycles of elliptic curves for recursive arguments

A *2-cycle of elliptic curves* is a pair of elliptic curves $E_1/\mathbb{F}_p$ and $E_2/\mathbb{F}_q$ with $p\ne q$ prime such that $\#E_1(\mathbb{F}_p)=q$ and $\#E_2(\mathbb{F}_q)=p$. Thus the scalar field of each curve's group is the base field of the other, so a circuit over $\mathbb{F}_q$ (the scalar field of $E_1$) can natively perform group operations on $E_2$ and vice versa. In folding-based recursion over a cycle, the primary circuit (over $\mathbb{F}_q$) verifies folds of commitments in $E_2$-friendly form and a secondary circuit handles the remaining non-native scalar multiplications.

## Sources

- Wilson Nguyen, Dan Boneh, Srinath Setty, "Revisiting the Nova Proof System on a Cycle of Curves", AFT (2023).
- Abhiram Kothapalli, Srinath Setty, "CycleFold: Folding-scheme-based Recursive Arguments over a Cycle of Elliptic Curves", IACR ePrint 2023/1192 (2023).
