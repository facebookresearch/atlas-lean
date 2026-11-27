# The interactive response time law

Consider an interactive system with $N$ users at terminals, each of whom at every time is either thinking or waiting for the system to respond to an interaction, observed over an interval of length $T$ in which $C > 0$ interactions complete. Let $R$ be the accumulated time users spent waiting for the system divided by $C$ (the average response time), $Z$ the accumulated thinking time divided by $C$ (the average think time), and $X = C/T$ the throughput. Then

$$
N = X(R + Z), \qquad \text{that is,} \qquad R = \frac{N}{X} - Z,
$$

since the accumulated time of all users, $NT$, is the sum $CR + CZ$ of the waiting and thinking times. For example, with $64$ users, think time $30$ seconds and throughput $2$ interactions per second, the response time is $64/2 - 30 = 2$ seconds.

## Depends on

- [Operational quantities of an observation interval](operational-quantities-of-an-observation-interval.md)

## Sources

- E. D. Lazowska, J. Zahorjan, G. S. Graham and K. C. Sevcik, *Quantitative System Performance: Computer System Analysis Using Queueing Network Models*, Prentice-Hall, 1984, online edition <https://homes.cs.washington.edu/~lazowska/qsp/>, Chapter 3, Section 3.3 (Little's law applied to the entire system with its terminals, $N = X(R + Z)$, the response time law and its example).
