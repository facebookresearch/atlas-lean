# Nim-sum zero via the last pile

For natural numbers $a_1, \dots, a_n$ (the preceding piles)
and $b$ (the last pile), the nim-sum $a_1 \oplus \cdots \oplus a_n \oplus b$ is $0$ if and only if
$b = a_1 \oplus \cdots \oplus a_n$, where $\oplus$ is bitwise exclusive or and the nim-sum of no
piles is $0$.

This is only the nim-sum identity behind the source's corollary. The corollary itself
characterizes P-positions; its game-theoretic content, that the nim-sum-zero positions are
exactly the P-positions, is Bouton's theorem.

## Sources

- Tanya Khovanova and Joshua Xiong, "Nim Fractals," Journal of Integer Sequences 17 (2014), Article 14.7.8, Corollary, lines 163–165, https://cs.uwaterloo.ca/journals/JIS/VOL17/Khovanova/khova6.tex
