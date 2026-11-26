# Companion Binet formula for generalized Fibonacci sequences

Let $p$ be a real number and
let $W : \mathbb{Z} \to \mathbb{R}$ satisfy $W_{j+2} = p W_{j+1} + W_j$ for every integer $j$. Put
$\sigma = (p + \sqrt{p^2 + 4})/2$ and $\tau = (p - \sqrt{p^2 + 4})/2$. Then for every integer
$j$,

$$
(W_1 - W_0 \tau) \sigma^j + (W_1 - W_0 \sigma) \tau^j = W_{j+1} + W_{j-1}.
$$

Here $A = W_1 - W_0 \tau$ and $B = W_1 - W_0 \sigma$ are the Binet constants of $W$, so that
$W_j = (A \sigma^j - B \tau^j)/(\sigma - \tau)$.

## Sources

- Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of Integer Sequences 27 (2024), Article 24.6.2, Lemma 13 (`jis-2024-24.6.2-lem-13`).
