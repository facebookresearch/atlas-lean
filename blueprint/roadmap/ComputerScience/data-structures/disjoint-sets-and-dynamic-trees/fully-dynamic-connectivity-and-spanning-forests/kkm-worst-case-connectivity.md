# Kapron-King-Mountjoy: polylogarithmic worst-case dynamic connectivity against oblivious adversaries

There is a randomized fully dynamic connectivity data structure on $n$ vertices with worst-case time $O(\log^4 n)$ per edge insertion, $O(\log^5 n)$ per edge deletion and $O(\log n / \log \log n)$ per query. Every answer "connected" is correct, and every answer "not connected" is correct with high probability; the guarantee holds against an oblivious adversary.

## Proof sketch

Maintain a spanning forest in Euler-tour trees together with, for each of $O(\log n)$ sampling levels and $O(\log n)$ independent repetitions, the XOR sketches of incident non-tree edges summed over each tree. After a tree-edge deletion, the XOR of the sketches over one of the two resulting trees, at a sampling level where exactly one cut edge survives, returns the name of a replacement edge with constant probability, and repetitions amplify this; each candidate name is tested against the graph in $O(\log n/\log\log n)$ time, so a wrong name is never used. A hierarchy of $O(\log n)$ Boruvka-like levels handles cascading splits, giving polylogarithmic worst-case time; the forest reveals information about the random sampling, which is why the adversary must be oblivious.

## Depends on

- [Oblivious and adaptive adversaries; amortized and worst-case update time](adversary-and-update-time-models.md)
- [Fully dynamic connectivity, spanning forest and minimum spanning forest problems](fully-dynamic-connectivity-problems.md)

## Proof depends on

- [Replacement edges after deleting a spanning-forest edge](replacement-edge-lemma.md)
- [XOR sketches recover a single edge of a vertex cut](xor-cutset-sketch-lemma.md)
- [Euler tour](../euler-tour-tree/tour.md)

## Sources

- Bruce M. Kapron, Valerie King, Ben Mountjoy, "Dynamic graph connectivity in polylogarithmic worst case time", SODA (2013).
- Zhengyu Wang, "An Improved Randomized Data Structure for Dynamic Graph Connectivity", arXiv:1510.04590, Section 1 (the update and query bounds and one-sided error of Kapron, King and Mountjoy).
- Danupon Nanongkai, Thatchaphol Saranurak, "Dynamic Spanning Forest with Worst-Case Update Time: Adaptive, Las Vegas, and O(n^{1/2-epsilon})-Time", STOC (2017), arXiv:1611.03745, abstract (the Kapron–King–Mountjoy structure assumes an oblivious adversary).
