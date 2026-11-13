# Uniqueness of the P-positions of a terminating impartial game

Write $x \to y$ when there is a
move from position $x$ to position $y$, and assume there is no infinite sequence of moves
$x_0 \to x_1 \to x_2 \to \cdots$. Call a set $P$ of positions stable if no move leads from a
position in $P$ to a position in $P$, and absorbing if from every position outside $P$ some move
leads to a position in $P$. Then any two stable and absorbing sets of positions are equal.

In particular the P-positions are determined by stability and absorption, and the N-positions
are their complement.

## Sources

- Antoine Renard and Michel Rigo, "Variants of Wythoff Game with Terminal Positions or Blocking Maneuvers," Journal of Integer Sequences 29 (2026), Article 26.1.6, Proposition (Folklore), lines 438–448, https://cs.uwaterloo.ca/journals/JIS/VOL29/Rigo/rigo5.tex; stability and absorption are defined in lines 430–436. Termination is encoded by the well-foundedness of the move relation on the acyclic game graph.
