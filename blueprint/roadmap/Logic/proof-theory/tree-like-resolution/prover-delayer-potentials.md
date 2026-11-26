# Prover–Delayer potentials bound tree-like refutation size

Let $\mu$ be a function from partial assignments to $\mathbb{N}$ such that for every partial assignment $\rho$ that falsifies no clause of $\varphi$ and every variable $v$ unset by $\rho$, $\mu(\rho) \le \mu(\rho[v{=}0]) + \mu(\rho[v{=}1])$, and $\mu(\rho) \ge 1$ only matters on non-falsifying $\rho$ (with $\mu = 0$ on falsifying ones). Then every tree-like resolution refutation of $\varphi$ has at least $\mu(\emptyset)$ leaves. Equivalently, a Delayer strategy scoring $\log_2 \mu(\emptyset)$ points in the asymmetric Prover–Delayer game forces tree-like refutations of size at least $\mu(\emptyset)$.

## Proof sketch

Walk a tree-like refutation from the root, maintaining a partial assignment falsifying the current clause: at a resolution step on an unset $v$, the two extensions of $\rho$ falsify the two premises. Induction on the tree shows the number of leaves below a node is at least $\mu$ of its falsifying assignment.

## Depends on

- [Tree-like resolution derivation](../../propositional-logic/resolution-size-and-width/resolution-tree.md)
- [Size of a tree-like derivation](../../propositional-logic/resolution-size-and-width/proof-size.md)

## Sources

- O. Beyersdorff, N. Galesi and M. Lauria, "A Lower Bound for the Pigeonhole Principle in Tree-Like Resolution by Asymmetric Prover–Delayer Games", Information Processing Letters 110(23), 1074–1077, 2010.
