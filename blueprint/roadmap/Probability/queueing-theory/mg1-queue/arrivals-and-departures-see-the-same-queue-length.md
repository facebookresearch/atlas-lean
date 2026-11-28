# Arrivals and departures see the same queue length

Consider any queueing system, on any sample path, in which customers arrive one at a time and leave one at a time, and let $L(t)$ be the number present. For $n \ge 0$ and $t \ge 0$ let $A_n(t)$ be the number of arrivals in $[0, t]$ that find $n$ customers present and $D_n(t)$ the number of departures in $[0, t]$ that leave $n$ behind. Then

$$
|A_n(t) - D_n(t)| \le 1 ,
$$

since arrivals finding $n$ are exactly the up-crossings from $n$ to $n + 1$ and departures leaving $n$ the down-crossings from $n + 1$ to $n$, and the two alternate. Consequently, if the number of arrivals by time $t$ tends to infinity and the fractions $a_n = \lim_t A_n(t)/A(t)$ and $d_n = \lim_t D_n(t)/D(t)$ exist, where $A(t)$ and $D(t)$ are the total numbers of arrivals and departures with $A(t)/D(t) \to 1$, then $a_n = d_n$ for all $n$. With [Poisson arrivals see time averages](../poisson-arrivals-see-time-averages.md), in the stationary M/G/1 queue with $\lambda > 0$ and $\rho = \lambda E[B] < 1$, arrivals, departures and outside observers see the same distribution; without $\rho < 1$ there may be no stationary distribution at all, as for the M/M/1 queue with equal arrival and service rates.

## Proof depends on

- [Poisson arrivals see time averages](../poisson-arrivals-see-time-averages.md): only for the last sentence.

## Sources

- I. Adan and J. Resing, *Queueing Systems*, lecture notes, Eindhoven University of Technology, <https://www.win.tue.nl/~iadan/queueing.pdf>, Section 7.1 (the level-crossing argument that $a_n = d_n$ for any system where customers arrive and leave one by one, and $a_n = d_n = p_n$ for the M/G/1 queue) and Exercise 48.
