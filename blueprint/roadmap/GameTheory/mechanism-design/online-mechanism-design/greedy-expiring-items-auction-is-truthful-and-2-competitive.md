# Greedy expiring-items auction is truthful and 2-competitive

In the expiring-items environment, where one item is available in each period $t$ and expires at its end and each agent wants one item within its window, consider the greedy policy that in each period allocates the item to the highest-value present unallocated agent, breaking ties by a priority order of the agents fixed independently of the reported windows. It is causal and monotone; with critical payments it is truthful against misreports with no early arrival and no late departure, individually rational and makes no positive transfers, and its welfare is at least half the offline optimum.

## Proof sketch

Charge each agent served in the offline optimum but not by greedy to the agent greedy serves in the period in which the optimum serves it, which is present then and has at least the same value; charge an agent served by both to itself. Each greedy allocation is charged at most twice. For monotonicity, an agent that greedy does not serve in a period changes none of that period's decisions, so reporting an earlier arrival, a later departure or a higher value leaves the history unchanged until the agent is served.

## Depends on

- [Online mechanism with arrival and departure types](online-mechanism-with-arrival-and-departure-types.md)

## Proof depends on

- [Monotone online policies with critical payments are truthful](monotone-online-policies-with-critical-payments-are-truthful.md)

## Sources

- David C. Parkes, "Online Mechanisms", Algorithmic Game Theory, Cambridge University Press, 2007.
- Ron Lavi and Noam Nisan, "Competitive Analysis of Incentive Compatible On-Line Auctions", Proceedings of the 2nd ACM Conference on Electronic Commerce, 2000.
