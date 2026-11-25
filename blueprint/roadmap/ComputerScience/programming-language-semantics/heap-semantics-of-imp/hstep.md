# Small-step semantics of heap commands

The single-step relation
$(c, s, h) \to (c', s', h')$ on heap configurations is the least relation closed under the rules
below. Here $a(s)$ is the value of an expression $a$ in the store $s$, $s[x \mapsto n]$ is $s$
with variable $x$ set to $n$, $h[\ell \mapsto n]$ is $h$ with address $\ell$ set to $n$, and
$h \setminus \ell$ is $h$ with address $\ell$ removed.

- Assignment: $(x := a, s, h) \to (\mathbf{skip}, s[x \mapsto a(s)], h)$.
- Sequence: $(\mathbf{skip}; c_2, s, h) \to (c_2, s, h)$, and if
  $(c_1, s, h) \to (c_1', s', h')$ then $(c_1; c_2, s, h) \to (c_1'; c_2, s', h')$.
- Conditional: $(\mathbf{if}\ b\ \mathbf{then}\ c_1\ \mathbf{else}\ c_2, s, h)$ steps to
  $(c_1, s, h)$ if $b(s)$ is true and to $(c_2, s, h)$ if $b(s)$ is false.
- Loop: $(\mathbf{while}\ b\ \mathbf{do}\ c, s, h)$ steps to
  $(\mathbf{if}\ b\ \mathbf{then}\ d\ \mathbf{else}\ \mathbf{skip}, s, h)$, where $d$ is the
  sequence $c; \mathbf{while}\ b\ \mathbf{do}\ c$.
- Read: if $h$ maps the address $a(s)$ to $v$, then
  $(x := [a], s, h) \to (\mathbf{skip}, s[x \mapsto v], h)$.
- Write: if $a(s)$ is allocated in $h$, then
  $([a] := e, s, h) \to (\mathbf{skip}, s, h[a(s) \mapsto e(s)])$.
- Allocation: for every address $\ell$ not allocated in $h$,
  $(x := \mathbf{alloc}(e), s, h) \to (\mathbf{skip}, s[x \mapsto \ell], h[\ell \mapsto e(s)])$.
- Deallocation: if $a(s)$ is allocated in $h$, then
  $(\mathbf{free}(a), s, h) \to (\mathbf{skip}, s, h \setminus a(s))$.
