# The image of the Dumont–Thomas complement representation

Let $\eta$ be a substitution
on an alphabet $A$, and let $u : \mathbb{Z} \to A$ be a two-sided periodic point of $\eta$
whose least period is $p$ and whose seed letters $u_{-1}$ and $u_0$ are growing
($|\eta^k(u_{-1})| \to \infty$ and $|\eta^k(u_0)| \to \infty$ as $k \to \infty$). Let
$\mathcal{A}_{\eta,s}$ be the automaton of the seed $s = u_{-1}|u_0$. A word $w$ of natural
numbers is the Dumont–Thomas complement representation $\mathrm{rep}_u(n)$ (with respect to
$\eta$, $u$ and $p$) of some $n \in \mathbb{Z}$ if and only if $w$ lies in the image language
of $\eta$, $u$ and $p$: the length of $w$ is $\ell p + 1$ for some $\ell \in \mathbb{N}$,
$\mathcal{A}_{\eta,s}$ accepts $w$, and $w$ starts neither with $0\,0^p$ nor with
$1\,\mathrm{last}_{\eta,p}(u_{-1})$, where $\mathrm{last}_{\eta,p}(u_{-1})$ is the digit word
along last letters with $p$ steps starting from $u_{-1}$.

## Sources

- Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24 (2024), Article A112, Lemma 8.3.
