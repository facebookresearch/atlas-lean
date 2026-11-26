# Second welfare theorem for combinatorial auctions

If an allocation $S$ (viewed as an integral vector) is an optimal solution of the LP relaxation, then there are item prices $p$ such that $(S, p)$ is a Walrasian equilibrium; the prices are given by an optimal dual solution. This holds for arbitrary real valuations, and for $0$-$1$ optimal LP vectors under $v_i(\emptyset) \ge 0$.

## Proof sketch

Strong LP duality gives an optimal dual $(u, p)$ with equal objective; complementary slackness says each allocated bundle attains $u_i$, so it is demanded at prices $p$, and items not allocated have zero price.

## Depends on

- [Combinatorial auction LP relaxation and Walrasian equilibrium](combinatorial-auction-lp-relaxation-and-walrasian-equilibrium.md)

## Sources

- Liad Blumrosen and Noam Nisan, "Combinatorial Auctions", Algorithmic Game Theory, Cambridge University Press, 2007.
