# Up-step probability of the Moran process

For a real number $r$ and natural numbers $N$ and $i$, let

$$a_i = \frac{r i}{r i + (N - i)} \cdot \frac{N - i}{N},$$

computed in the real numbers (so $N - i < 0$ when $i > N$), with the convention that division by $0$ gives $0$. For $r > 0$ and $i \le N$, it is the probability that one step of the Moran process with $N$ individuals and mutant relative fitness $r$ takes the mutant count from $i$ to $i + 1$: a mutant is chosen to reproduce, with probability $r i/(r i + N - i)$, and a wild type is chosen to die, with probability $(N - i)/N$.
