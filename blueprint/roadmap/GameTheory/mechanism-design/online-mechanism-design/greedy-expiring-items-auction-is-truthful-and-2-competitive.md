# Greedy expiring-items auction is truthful and 2-competitive

In the expiring-items environment, where $c_t$ identical units are available in period $t$ and expire at its end and each agent wants one unit within its window, the greedy policy that in each period allocates the available units to the highest-value present unallocated agents is causal and monotone; with critical payments it is truthful, individually rational and makes no positive transfers, and its welfare is at least half the offline optimum.

## Proof sketch

Charge each unit allocated in the offline optimum but not by greedy to the greedy allocation in the same period, which has at least the same value, or to the agent itself if greedy allocated it elsewhere; each greedy allocation is charged at most twice.

## Depends on

- [Online mechanism with arrival and departure types](online-mechanism-with-arrival-and-departure-types.md)

## Proof depends on

- [Monotone online policies with critical payments are truthful](monotone-online-policies-with-critical-payments-are-truthful.md)

## Sources

- David C. Parkes, "Online Mechanisms", Algorithmic Game Theory, Cambridge University Press, 2007.
- Ron Lavi and Noam Nisan, "Competitive Analysis of Incentive Compatible On-Line Auctions", Proceedings of the 2nd ACM Conference on Electronic Commerce, 2000.
