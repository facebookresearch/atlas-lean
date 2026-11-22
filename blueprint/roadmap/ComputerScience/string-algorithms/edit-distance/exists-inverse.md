# Every edit script has an inverse of the same cost

Let $x$ and $y$ be lists over a type whose Boolean equality test agrees with equality. If an edit
script $E$ transforms $x$ into $y$, then some edit script transforms $y$ into $x$ and has the same
unit cost as $E$ (for instance, the script obtained by swapping insertions and deletions and
reversing substitutions).
