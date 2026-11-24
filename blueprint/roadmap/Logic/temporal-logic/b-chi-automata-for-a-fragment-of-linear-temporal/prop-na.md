# Büchi automaton for a propositional formula

For a propositional formula $\varphi$, this
Büchi automaton over letters that are sets of atoms has a start state $u$ and two verdict states
$t$ and $f$, of which only $t$ is accepting. From $u$, on a letter $s$ it moves to $t$ if
$\varphi$ evaluates to true at $s$ and to $f$ otherwise; from $t$ and from $f$ it stays in the
same state on every letter. So it records the verdict of $\varphi$ on the first letter.
