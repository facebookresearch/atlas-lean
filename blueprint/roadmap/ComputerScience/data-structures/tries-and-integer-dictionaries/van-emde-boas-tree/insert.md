# Insertion into a van Emde Boas tree

Let $m$ be a natural number, let $t$ be a van Emde
Boas tree over the universe $\{0, 1, \dots, m^2 - 1\}$ and let $x$ be an element of the
universe. Inserting $x$ into $t$ gives the tree obtained from $t$ by setting bit $x \bmod m$ of
cluster $\lfloor x / m \rfloor$ and summary bit $\lfloor x / m \rfloor$, leaving every other bit
unchanged.
