# Uniform end-of-sequence probability forces termination

Let a next-token kernel over a finite token set assign to each prefix a distribution on tokens and an end-of-sequence (EOS) symbol. If the EOS probability is at least $\varepsilon > 0$ at every prefix, then the mass $s_n$ of strings not yet terminated after $n$ steps satisfies $s_n \le (1 - \varepsilon)^n$ for every $n$, and the total mass of terminated finite strings is $1$.
