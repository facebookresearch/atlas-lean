# The $b$-ary multinomial coefficient

Let $b \ge 2$, let $n$ be a natural number and let
$(k_1, \dots, k_m)$ be a list of natural numbers, and write $n_l$ and $(k_i)_l$ for the rank-$l$
base-$b$ digits of $n$ and $k_i$ (taken to be $0$ beyond the last digit, with $0$ having no
digits). Let $N$ be the largest of the numbers of base-$b$ digits of $n, k_1, \dots, k_m$. The
$b$-ary multinomial coefficient of $n$ over $(k_1, \dots, k_m)$ is $\prod_{l=0}^{N-1} c_l$, where
$c_l = \frac{n_l!}{(k_1)_l! \cdots (k_m)_l!}$ if $(k_1)_l + \dots + (k_m)_l = n_l$ and $c_l = 0$
otherwise.

## Sources

- concept `jis_term_48a88a0d7fe1b70bcdb0254d`, semantic child `jis_sem_8f93866ba77d801d9ead13ca` (`b-ary multinomial coefficient`), atomic coefficient definition of source statement `jis_2dd3152b04bd3c701907ca5c` (byte-identical duplicate `jis_40ae94aec46faf8f37032d00`).
- https://cs.uwaterloo.ca/journals/JIS/VOL19/Jiu/jiu3.tex (`df0640a5d745b80e57565a61040414d4305680a9a5700ce376a717ffdc6f2571`), span bytes/chars 16014..16622, lines 349..359, raw TeX SHA-256 `ce098c5865cf6b3b380b6a679820635672ac58a52901ab8de41afd2c8a54d46b`.
