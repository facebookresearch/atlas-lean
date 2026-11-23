# Recurrence for the last-letter digit word

Let $\eta$ map each letter of an alphabet $A$
to a finite word over $A$. For a natural number $j$ and a letter $e \in A$, the last-letter
digit word of $j$ steps from $e$ is obtained by repeating the following step $j$ times, starting
at $e$ and stopping early if the image of the current letter is empty: from the current letter
$x$, record the digit $|\eta(x)| - 1$ and move to the last letter of $\eta(x)$. Let $c, d \in A$
and let $k$ be a natural number. If $\eta(c)$ is nonempty and its last letter is $d$, then the
last-letter digit word of $k + 1$ steps from $c$ is the digit $|\eta(c)| - 1$ followed by the
last-letter digit word of $k$ steps from $d$.

## Sources

- Labbé and Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24 (2024), Article A112, Section 7.
