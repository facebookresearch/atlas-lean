# Neutral words of the seed automaton

Let $\eta$ be a substitution on an alphabet $A$,
and let $u : \mathbb{Z} \to A$ be a two-sided periodic point of $\eta$ whose least period is
$p$ and whose seed letters $u_{-1}$ and $u_0$ are growing ($|\eta^k(u_{-1})| \to \infty$ and
$|\eta^k(u_0)| \to \infty$ as $k \to \infty$). Let $\mathcal{A}_{\eta,s}$ be the automaton of
the seed $s = u_{-1}|u_0$, let $W_{\min} = 0^p$, and let
$W_{\max} = \mathrm{last}_{\eta,p}(u_{-1})$ be the digit word along last letters with $p$ steps
starting from $u_{-1}$. Then for every word $v$ of natural numbers and every $i \in \mathbb{N}$:
if $\mathcal{A}_{\eta,s}$ accepts $0v$, then it accepts $0\,W_{\min}^i\,v$ with the same output;
and if $\mathcal{A}_{\eta,s}$ accepts $1v$, then it accepts $1\,W_{\max}^i\,v$ with the same
output.

## Sources

- Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24 (2024), Article A112, Lemma 7.1.
