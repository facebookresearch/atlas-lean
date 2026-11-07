# Iterates of the period-doubling substitution

Write the period-doubling substitution
$a \mapsto ab$, $b \mapsto aa$ over the letters $a = 1$ and $b = 0$, so that it sends $1$ to $10$
and $0$ to $11$. The $n$-th period-doubling iterate is the word obtained by applying this
substitution $n$ times to the one-letter word $1$; the iterates begin $1$, $10$, $1011$,
$10111010$, and their limit is the period-doubling word (Walnut's PD).

The source's prose takes $a = 0$ and $b = 1$, but its Walnut definition `antifib`
(`PD[k]=@1` gives $9 + 10k$) and its displayed anti-Fibonacci numbers $0, 3, 9, 13, \ldots$ need
the first letter of PD to be $1$.

## Sources

- Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8, Section 4.
