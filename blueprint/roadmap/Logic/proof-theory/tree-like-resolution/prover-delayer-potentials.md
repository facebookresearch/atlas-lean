# Prover–Delayer potentials bound tree-like refutation size

In the asymmetric Prover–Delayer game on an unsatisfiable CNF formula $\varphi$, the players build a partial assignment until it falsifies a clause of $\varphi$; in each round Prover names a variable $x$, and Delayer either sets it (scoring nothing) or lets Prover set it, scoring $\log_2 c_0(x,\alpha)$ if Prover chooses $0$ and $\log_2 c_1(x,\alpha)$ if Prover chooses $1$, where $\alpha$ is the current assignment and the weights satisfy $1/c_0(x,\alpha) + 1/c_1(x,\alpha) = 1$ for all $x, \alpha$. If $\varphi$ has a tree-like resolution refutation of size at most $S$, then Prover has a strategy holding Delayer to at most $\log_2 S$ points. Equivalently, a Delayer strategy that guarantees $p$ points forces every tree-like refutation to have size at least $2^p$. With $c_0 = c_1 = 2$ this is the symmetric game of Pudlák and Impagliazzo.

## Proof sketch

View the refutation as a decision tree $\Pi$ (same number of nodes). Prover keeps the invariant $|\Pi_{\alpha}| \le |\Pi| / 2^{p}$ for the subtree $\Pi_\alpha$ reached by the current assignment $\alpha$ after Delayer has $p$ points: when Delayer defers on $x$, Prover picks the value $j$ with $|\Pi_{\alpha[x=j]}| \le |\Pi_\alpha| / c_j(x,\alpha)$, which exists because $1/c_0 + 1/c_1 = 1$. At the end the subtree is a single leaf.

## Depends on

- [Tree-like resolution derivation](../../propositional-logic/resolution-size-and-width/resolution-tree.md)
- [Size of a tree-like derivation](../../propositional-logic/resolution-size-and-width/proof-size.md)

## Proof depends on

- [Tree-like derivations versus line-based resolution proofs](tree-like-versus-dag-like-resolution.md)

## Sources

- O. Beyersdorff, N. Galesi and M. Lauria, "A Lower Bound for the Pigeonhole Principle in Tree-Like Resolution by Asymmetric Prover–Delayer Games", Information Processing Letters 110(23), 1074–1077, 2010: Section 3, Theorem 1 and its proof.
