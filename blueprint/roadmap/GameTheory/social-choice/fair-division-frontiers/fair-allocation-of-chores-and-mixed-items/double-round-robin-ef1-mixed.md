# The double round-robin algorithm gives EF1 for mixed items

In the mixed fair division model with additive utilities, consider the double round-robin algorithm: let $M^- = \{ o : u_i(o) \le 0 \text{ for all } i \}$ be the items that no agent values positively; agents first pick items of $M^-$ in round-robin order $1, \dots, n$, after padding $M^-$ with dummy items of utility $0$ so that $\lvert M^- \rvert$ is a multiple of $n$; then agents pick the remaining items in the reverse round-robin order $n, \dots, 1$, each agent passing (picking a dummy item of utility $0$) when no remaining item has positive utility for her; every remaining item is positive for some agent, so all items are eventually allocated. The resulting allocation is EF1.

## Proof sketch

Within each phase, an agent who picks earlier than another faces envy at most one item: in the chores phase an agent picking before $j$ envies $j$ by at most her own last chore, and in the goods phase the order is reversed so that agents disadvantaged in the first phase pick first in the second. Combining the two phases, every pair's envy is eliminated by removing either the first good taken by $j$ or the last chore taken by $i$.

## Depends on

- [Fair division of mixed goods and chores](mixed-goods-and-chores-model.md)

## Proof depends on

- [Round-robin allocation is envy-free up to one good](../../../cooperative-games/fair-division-of-indivisible-goods/round-robin-allocation-is-ef1.md)

## Sources

- H. Aziz, I. Caragiannis, A. Igarashi, T. Walsh, "Fair allocation of indivisible goods and chores", IJCAI 2019; Autonomous Agents and Multi-Agent Systems 36 (2022).
