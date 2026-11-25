# Linear reservoir with variable inflow

Let $T>0$. A linear reservoir with recession constant $k>0$ has storage $S$ and outflow $Q=kS$; let its inflow $I$ be continuous on
$[0,T]$. The unique solution, continuous on $[0,T]$ and satisfying $S'=I(t)-kS$ for $0<t<T$ with $S(0)=S_0$, is

$$S(t) = e^{-kt} S_0 + \int_0^t e^{-k(t - \tau)} I(\tau)\,d\tau, \qquad 0 \le t \le T,$$

so $Q(t)=kS_0e^{-kt}+\int_0^t k e^{-k(t-\tau)}I(\tau)\,d\tau$, and
$S(T) - S_0 = \int_0^T (I - Q)\,dt$. With nonnegative inflow and $S_0 \ge 0$ the storage stays nonnegative. Losses, periodic operation and
several reservoirs are separate problems.

## Depends on

## Proof depends on

- [Duhamel's formula (variation of constants)](../../../../Analysis/ordinary-differential-equations/duhamel-variation-of-constants.md)

## Sources

- J. Lebl, *Notes on Diffy Qs: Differential Equations for Engineers*, version 6.11, Section 1.4, linear first-order equations and the integrating factor, <https://www.jirka.org/diffyqs/>.
