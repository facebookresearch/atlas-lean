# The Dumont–Thomas image language

Let $\eta$ send each letter of an alphabet $A$ to a
finite word over $A$, let $u : \mathbb{Z} \to A$ and let $p \in \mathbb{N}$. Write
$\mathcal{A}_{\eta,s}$ for the seed automaton of $\eta$ with seed $s = u_{-1} | u_0$, and
$W_{\max}$ for the digit word obtained by following the last letter from $u_{-1}$ for at most
$p$ steps: at a letter $c$ it records $|\eta(c)| - 1$ and moves to the last letter of
$\eta(c)$, stopping early if $\eta(c)$ is empty. The language is the set of finite words $w$
over $\mathbb{N}$ such that $|w| = \ell p + 1$ for some $\ell \in \mathbb{N}$, $w$ is accepted
by $\mathcal{A}_{\eta,s}$, $w$ does not start with the word $0 0^p$, and $w$ does not start
with the word $1 W_{\max}$.

## Sources

- Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24 (2024), Article A112, Lemma 8.3 and Theorem 8.4.
