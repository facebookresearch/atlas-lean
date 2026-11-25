# The difference lemma

Let $\mu$ be a probability distribution on a set $\Omega$, and let $A, B, F : \Omega \to \{0, 1\}$ with
$A(\omega) = B(\omega)$ whenever $F(\omega) = 0$. Then the distinguishing advantage between the games
$A(\omega)$ and $B(\omega)$, for $\omega$ drawn from $\mu$, is at most $\Pr[F(\omega) = 1]$: games that
are identical until a bad event differ by at most its probability (Shoup, Lemma 1; Boneh and Shoup,
Theorem 4.7).
