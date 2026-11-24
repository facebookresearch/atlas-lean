# Cost bounds for the modular linear equation solver

Let $a > 0$ and $n > 0$ be natural
numbers, $b$ an integer and $d = \gcd(a, n)$, and put $c = 4 + 3d$ if $d \mid b$ and $c = 0$
otherwise. The cost $T$ of the modular linear equation solver on $a$, $b$, $n$ satisfies
$1 + c \le T \le 6(2 \lfloor \log_2 n \rfloor + 2) + 1 + c$.

The cost counts arithmetic events, so this is the $O(\log n + \gcd(a, n))$ bound of the source.
