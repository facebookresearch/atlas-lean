# Banded alignment is exact when some optimal alignment is banded

Let $\sigma$ be an
integer substitution score on an alphabet, $g$ an integer gap score and $w \in \mathbb{N}$ a
band width. For sequences $x$ and $y$ over the alphabet, if some alignment of $x$ and $y$ is
banded with width $w$ and has score (under $\sigma$ and $g$) equal to the Needleman–Wunsch
score of $x$ and $y$, then the banded score of $x$ and $y$ (under $\sigma$, $g$ and width $w$)
is defined and equals their Needleman–Wunsch score.
