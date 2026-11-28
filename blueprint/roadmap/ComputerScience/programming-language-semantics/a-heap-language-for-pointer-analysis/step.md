# Small-step semantics of the heap language

The small-step relation of the allocation-site heap language on configurations (statement, store, heap):

- `new dst a` steps to `skip` with $s[\mathit{dst} := a]$ and $h[a := 0]$ (allocation is not fresh);
- `copy dst src` steps to `skip` with $s[\mathit{dst} := s(\mathit{src})]$;
- `load dst src` steps to `skip` with $s[\mathit{dst} := h(s(\mathit{src}))]$;
- `store dst src` steps to `skip` with $h[s(\mathit{dst}) := s(\mathit{src})]$;
- `skip; next` steps to `next` with store and heap unchanged;
- `first; second` steps to `first'; second` with the updated store and heap of a step of `first` to `first'`.

Anything a rule does not mention is unchanged, and `skip` has no step.
