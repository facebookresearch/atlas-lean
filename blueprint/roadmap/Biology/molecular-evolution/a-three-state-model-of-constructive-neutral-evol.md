# A three-state dependency model of constructive neutral evolution

Consider a continuous-time Markov chain with states $0$ (self-sufficient,
no partner interaction), $1$ (self-sufficient, gratuitous interaction), and
$2$ (dependent on the partner). Specify the rate matrix

$$Q=\begin{pmatrix}-a&a&0\\b&-(b+c)&c\\0&d&-d\end{pmatrix}.$$

These rates are model parameters. In an ideal origin-fixation
interpretation, neutral substitution rates can equal mutation rates after
mutation supply and neutral fixation cancel; that interpretation does not
itself prove a weak-mutation limit or fix a population clock.
The direct loss of the required interaction, $2\to0$, is inaccessible by
assumption. If $a,b,c,d>0$, the unique stationary probability vector is

$$\pi=\frac{(bd,ad,ac)}{bd+ad+ac},\qquad
 \frac{\pi_2}{\pi_0+\pi_1}=\frac{ac}{d(a+b)}.$$

In particular the odds also depend on $a/(a+b)$: a large $c/d$ alone
does not guarantee large odds if access to the interaction is very rare.
For $d=0$, $a,c>0$ and $b\ge0$, state2 is absorbing and is reached almost
surely from every state. Its mean hitting times are
$h_0=(a+b+c)/(ac)$, $h_1=(a+b)/(ac)$ and $h_2=0$.
For $d>0$, a visit to state2 lasts mean time $1/d$ and ends almost surely;
small positive reversal rate is not an inaccessible reversal.

## Depends on

- [Finite-state continuous-time Markov path](../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-path.md)

## Proof depends on

- [Detailed balance implies semigroup invariance](../../Probability/markov-chains/finite-continuous-time-markov-chains/stationarity-and-detailed-balance-for-finite-con/vec-mul-ctmc-transition.md)

## Expansion

The proposed weights satisfy $\pi_0a=\pi_1b$ and $\pi_1c=\pi_2d$.
Conversely, the first and last coordinates of $\pi Q=0$ force those
relations, and normalization gives uniqueness. The directed path graph is
irreducible for positive rates. At any fixed positive time every entry
of its transition matrix is positive: the event of following the at-most-two
required jumps and no others has positive probability. A common positive
minorization then contracts differences of probability rows, proving
convergence to the stationary law.
When $d=0$, every visit to state1 has independent conditional probability
$c/(b+c)>0$ of jumping to state2, and state0 returns to1 at positive rate.
Thus absorption is almost sure. First-step conditioning gives
$h_0=1/a+h_1$ and $h_1=1/(b+c)+b h_0/(b+c)$, hence the finite means.
The return $2\to1$ regains self-sufficiency; it is not the lethal direct
loss $2\to0$, whose rate remains zero.

## Sources

- A. Stoltzfus, "Constructive neutral evolution: exploring evolutionary theory's curious disconnect", Biology Direct 7 (2012), 35, <https://doi.org/10.1186/1745-6150-7-35>, excess-capacity, duplication and splicing discussions. The three-state chain and its rates are an explicit derived model, not a claim that all constructive neutral evolution has these rates or is irreversible.
