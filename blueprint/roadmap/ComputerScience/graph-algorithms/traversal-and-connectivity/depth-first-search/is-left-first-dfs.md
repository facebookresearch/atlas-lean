# Left-first depth-first traversals

Let $G$ be a finite directed graph given by ordered
adjacency lists and let $r = (r_1, \dots, r_k)$ be a list of root vertices. A traversal $T$ is a
left-first DFS of $G$ from $r$ when some finite run of the following machine ends with an empty
work list and with recorded preorder, postorder and (child, parent) list equal to those of $T$.

The machine holds a work list of frames, each either "enter $v$ with parent $p$" (where the parent
$p$ may be absent) or "exit $v$", a set of visited vertices, and the three recorded lists. It starts
with the frames "enter $r_1$ with no parent", ..., "enter $r_k$ with no parent", no visited vertex
and empty recorded lists. A step removes the first frame of the work list. For "exit $v$" it
appends $v$ to the postorder. For "enter $v$ with parent $p$" it does nothing more if $v$ is
visited; otherwise it marks $v$ visited, appends $v$ to the preorder, appends $(v, p)$ to the
(child, parent) list if $p$ is present, and puts in front of the remaining work the frames
"enter $w$ with parent $v$" for the entries $w$ of the adjacency list of $v$, in order, followed by
"exit $v$".
