# Recursive Snaky certificate data and row invariants

Let $S=\{(0,0),(1,0),(2,0),(3,0),(3,1),(4,1)\}$. In table order $0,\ldots,7$, the symmetries send $(x,y)$ to $(x,y),(y,x),(x,-y),(-y,x),(-x,y),(y,-x),(-x,-y),(-y,-x)$, respectively. The [pinned certificate table](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SnakyCertificate.lean#L48-L1337) has rows indexed 6 through 615; each row is a nonempty list of terms consisting of a child index, one symmetry number, and two decimal digits $a,b$ giving translation $(a-4,b-4)$, applied **after** the numbered symmetry. The fixed array is indexed at row index minus six. The table is valid (exactly 610 entries in order, all children earlier), with exactly 1837 terms.

The six base rows translate $S$ so that the corresponding member in its displayed order is at the origin, take this envelope $H$, require $A=H\setminus\{0\}$ and have height 1. For a nonbase row transform each earlier child $(A_j,H_j,h_j)$ by that term; take $A=(\bigcup_j A_j\cup\bigcap_j H_j)\setminus\{0\}$, $H=\{0\}\cup\bigcup_j H_j$, and height $1+\max_j h_j$. Every row below 616 has $A\subseteq H$, $0\in H\setminus A$ and height at most 34. The following rows additionally have exactly the indicated singleton required set, envelope size, height, and disjointness from the forbidden cells:

- 557: $\{(-1,0)\}$, 118, 19, avoid $\{(x,y):x\le-3,\ y\le-2\}$.
- 595: $\{(-1,0)\}$, 222, 27, avoid $\{(x,y):x=-2,\ y\le-2\}$.
- 603: $\{(-1,0)\}$, 275, 27, avoid $\{(x,y):x\le-3,\ y=0\}$.
- 615: $\{(1,0)\}$, 686, 34, avoid $\{(1,-1)\}$.

## Depends on

- The complete table in the pinned comparator, labelled transforms and finite required/envelope/height recursion. The theorem checks that particular table, not an existential substitute.

## Proof depends on

- Table validity and placement count, extremal row evaluations and global row invariants.

## Expansion

Use the fixed numeric table and decoder, verify array offsets and earlier-child bounds, then recompute rows in increasing index order with a checked native evaluator. Transport avoidance of each infinite region to the finite check of every cell in the row envelope. Only after the table and recursion are represented with checked agreement can this be a native even if computationally local result. No proof of a game strategy is claimed by the table checks alone.

## Sources

- [Comparator statement: `OAI.SnakyCertificate.certificate_correct`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SnakyCertificate.lean#L1387-L1395)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/187.md)
- [Verified table outputs and assembly in the source model](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/SnakyCertificate/Main.lean)
- [Shape, exact numbered symmetries and digit decoder](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SnakyCertificate.lean#L13-L45)
- [Fixed 610-row data array and index convention](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SnakyCertificate.lean#L48-L1337)
- [Validity, recursive row evaluation and invariants](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SnakyCertificate.lean#L1339-L1385)
