# LZ78 phrases and tokens with fuel

For a list of phrases $D$, a finite list $x$ and a
natural number $n$ (the fuel), the result is the pair of empty lists when $n = 0$ or $x$ is
empty. Otherwise, with `(w, t, x')` the next phrase of $x$ from the empty phrase
(`LZ78.nextAux D [] x`), it is the result for the list `D ++ [w]`, the rest $x'$ and the fuel
$n - 1$, with $w$ put in front of its phrases and $t$ in front of its tokens. Each step consumes
at least one symbol, so the fuel $|x| + 1$ parses all of $x$.
