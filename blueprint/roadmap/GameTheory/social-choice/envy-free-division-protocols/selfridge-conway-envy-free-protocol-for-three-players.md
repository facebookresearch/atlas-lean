# Selfridge–Conway envy-free protocol for three players

For three players with nonatomic, finitely additive valuations of the cake $[0, 1]$, the Selfridge–Conway protocol (player $0$ cuts into three equal pieces by its measure; player $1$ trims its favourite piece to tie its second favourite if needed; players choose in the order $2, 1, 0$ with a constraint on the trimmed piece; the trimmings are divided by a second round of cutting and choosing) produces an envy-free and hence proportional division, using at most five cuts, so the cake is divided into at most six intervals.

## Proof sketch

In the first stage every player receives a piece it values at least as much as any other piece of the trimmed cake. The trimmings are divided so that the player among $1$ and $2$ who did not receive the trimmed piece cuts them into three equal pieces by its measure, and the receiver of the trimmed piece, then player $0$, then the cutter choose, and the player who made the first cut cannot envy the receiver of the trimmed piece on the trimmings because that piece plus trimmings was worth exactly a third to it.

## Depends on

- [Cake cutting in the Robertson-Webb query model](../cake-cutting-in-the-robertson-webb-query-model.md)
- [Cut-and-choose and Dubins-Spanier](../cut-and-choose-and-dubins-spanier.md)

## Sources

- Steven J. Brams and Alan D. Taylor, "An Envy-Free Cake Division Protocol", The American Mathematical Monthly, 1995.
- Jack Robertson and William Webb, "Cake-Cutting Algorithms: Be Fair If You Can", A K Peters, 1998.
