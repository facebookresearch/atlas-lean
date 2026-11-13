# The period-doubling word

For a natural number $k$, the letter at index $k$ (indices start
at $0$) of the period-doubling word is the letter at index $k$ of the word obtained by applying
the period-doubling substitution $1 \mapsto 10$, $0 \mapsto 11$ to the one-letter word $1$ a total
of $\lfloor \log_2 k \rfloor + 1$ times, where $\lfloor \log_2 0 \rfloor$ is taken to be $0$.
That word has length $2^{\lfloor \log_2 k \rfloor + 1} \le 2k + 2$, so it contains index $k$.

## Sources

- Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8, Section 4.
