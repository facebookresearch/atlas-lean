# Tilings of intermediate-code trees

Let intermediate code be given as trees whose nodes are labelled by operators (such as $\mathit{ADD}$, $\mathit{MUL}$, $\mathit{MEM}$, $\mathit{MOVE}$ and constants), and fix a finite set of *tiles*. A tile is a tree pattern: a tree of operators some of whose leaves are *holes*, standing for arbitrary subtrees. Each tile carries an instruction sequence and a cost. A tile for an expression computes the value of the pattern into a result temporary from temporaries holding the values of its holes; a tile for a statement, such as a $\mathit{MOVE}$ or a conditional jump, performs the effect of the statement or its transfer of control and produces no result.

- A tile *matches* at a node if the pattern agrees with the tree rooted there, with each hole matched to some subtree.
- A *tiling* of a tree chooses a tile matching at the root and, recursively, a tiling of each subtree matched by a hole. The subtrees are joined to the tile through fresh temporaries.
- The *code* of a tiling concatenates the code of the subtrees' tilings with the instruction sequence of the tile at the root. Its *cost* in the additive model is the sum of the costs of the tiles used.

A tile set is *complete* if every tree the compiler can produce has a tiling, which holds when every operator alone, with holes for its operands, is a tile. *Greedy tiling*, also called maximal munch, chooses at each node the matching tile of highest priority, usually the largest, and tiles the uncovered subtrees recursively.

## Sources

- A. C. Myers, *Instruction Selection*, lecture notes for CS 4120, Cornell University, 2022, <https://courses.cs.cornell.edu/courses/cs4120/2022sp/notes/tiles/index.html>: sections "Mapping instructions to tiles" (tiles for assembly instructions, completeness by a tile for each IR node), "Tiles as translations" (tiling as a translation relation $\mathcal{T}[\![t, e]\!]$ with uncovered subexpressions translated into fresh temporaries) and "Greedy tiling" (maximal munch).
