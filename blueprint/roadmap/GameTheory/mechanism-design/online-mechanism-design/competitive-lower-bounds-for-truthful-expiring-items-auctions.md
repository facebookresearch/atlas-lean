# Competitive lower bounds for truthful expiring-items auctions

No deterministic truthful online mechanism for expiring items achieves a competitive ratio better than $2$ against the offline optimum, and if agents may misreport departures arbitrarily (late departure allowed), no deterministic truthful mechanism achieves any constant competitive ratio.

## Proof sketch

An adversary presents an agent and, depending on whether it is allocated, follows with a higher-value agent in the same or the next period; truthfulness forces the decision to be made without knowing the future.

## Depends on

- [Online mechanism with arrival and departure types](online-mechanism-with-arrival-and-departure-types.md)

## Sources

- David C. Parkes, "Online Mechanisms", Algorithmic Game Theory, Cambridge University Press, 2007.
- Ron Lavi and Noam Nisan, "Competitive Analysis of Incentive Compatible On-Line Auctions", Proceedings of the 2nd ACM Conference on Electronic Commerce, 2000.
