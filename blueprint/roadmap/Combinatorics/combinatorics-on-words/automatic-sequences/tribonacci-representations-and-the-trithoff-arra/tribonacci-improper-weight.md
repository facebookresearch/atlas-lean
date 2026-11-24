# Weight of an improper word

Let $w$ be a word of natural-number digits, written most
significant digit first, and let $v = 0w$ be $w$ padded with a $0$ on the left, with positions
numbered from $0$. Let $p$ be the position of the leftmost digit $\ge 2$ of $v$ (the improper
boundary), or the length of $v$ if there is no such digit. The weight of $w$ is the sum of all
digits of $v$ from the position just after the last $0$ of $v$ before position $p$ to the end of
$v$; that is, the digits of the maximal run of nonzero digits ending just before position $p$,
together with all digits at positions $p$ and beyond.

## Sources

- Eric Chen, Adam Ge, Andrew Kalashnikov, Ella Kim, Evin Liang, Mira Lubashev, Matthew Qian, Rohith Raghavan, Benjamin Taycher, Samuel Wang and Tanya Khovanova, *Generalizing the Wythoff Array and Other Fibonacci Facts to Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4, Section 6.1, https://cs.uwaterloo.ca/journals/JIS/VOL28/Khovanova/khova43.html
