# De Bruijn graph compaction by vertex states

Maximal unitigs of a bidirected de Bruijn graph are determined entirely by which $k$-mers are their endpoints. That endpoint (flanking) property depends only on a bounded summary of the edges incident to each side of each vertex, so compaction can be done by tracking a small finite state per $k$-mer instead of storing the edges.

- [Flanking vertices and the vertex-side state automaton](flanking-vertices-and-the-vertex-side-state-automaton.md)
