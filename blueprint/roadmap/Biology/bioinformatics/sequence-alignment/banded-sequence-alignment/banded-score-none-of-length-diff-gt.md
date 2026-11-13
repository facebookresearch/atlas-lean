# No banded score when the lengths differ by more than the band width

Let $\sigma$ be
an integer substitution score on an alphabet, $g$ an integer gap score and $w \in \mathbb{N}$ a
band width. For sequences $x$ and $y$ over the alphabet, of lengths $m$ and $n$, with
$w < |m - n|$, the banded score of $x$ and $y$ (under $\sigma$, $g$ and width $w$) is undefined:
no alignment of $x$ and $y$ is banded with width $w$.
