# Few inputs lack a second preimage, and inversion is at most twice as easy as second preimages

Let $H : \{0,1\}^m \to \{0,1\}^n$ with $m \ge n$. (a) At most a $2^{n-m}$ fraction of inputs $x$ have no $x' \ne x$ with $H(x') = H(x)$. (b) For every inverter $A$ and the second-preimage finder $B(x) = A(H(x))$,

$$\Pr_x[A(H(x)) \in H^{-1}(H(x))] \le 2\,\Pr_x[B(x) \ne x,\ H(B(x)) = H(x)] + 2^{n-m}.$$

## Proof sketch

(a) Inputs without a sibling are alone in their fiber, so there are at most $2^n$ of them among $2^m$ inputs. (b) For $x$ in a fiber of size $c \ge 2$, the inverter's answer is independent of which element of the fiber was sampled, so it differs from $x$ with probability at least $1 - 1/c \ge 1/2$ times the inversion probability.

## Depends on

- [Second-preimage resistance](second-preimage-resistance.md)
- [Inversion experiment](../../security-games/asymptotic-security/invert-game.md)

## Sources

- P. Rogaway and T. Shrimpton, "Cryptographic Hash-Function Basics: Definitions, Implications, and Separations for Preimage Resistance, Second-Preimage Resistance, and Collision Resistance", Fast Software Encryption (FSE 2004), Lecture Notes in Computer Science, Springer, 2004, pp. 371–388; Theorem 7(1) and its proof in Appendix B.1 (numbering of the authors' full version).
