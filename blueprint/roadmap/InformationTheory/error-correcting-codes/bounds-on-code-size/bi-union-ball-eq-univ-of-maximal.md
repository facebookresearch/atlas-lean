# A maximal code is covering

Let $C \subseteq \alpha^n$ be a code to which no word can be added without creating two
codewords at distance less than $d$: every word at distance at least $d$ from all codewords
already lies in $C$. Then the Hamming balls of radius $d - 1$ around the codewords cover
$\alpha^n$.

Indeed, a word outside all these balls is at distance at least $d$ from every codeword, so it
lies in $C$, hence in its own ball.

## Sources

- V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*, draft of August 26, 2025, equation (4.2) in the proof of Theorem 4.2.1.
