---
declaration: def
origin: cited
statement: formalized
lean: CPythonListsort.minrunInit
---

# `merge_init` minrun initialization

Transcribe only the adaptive-minrun portion of `merge_init`: start `mr_e` at
zero, increment it while `list_size >> mr_e >= MAX_MINRUN`, set `mr_mask` to
`(1 << mr_e) - 1`, set `mr_current` to zero, and retain `listlen`. The
unsuffixed `1` makes the mask expression have C type `int`; the selected v1
platform additionally fixes `int` at 32 bits, while `mr_mask` is a 64-bit
`Py_ssize_t`. Model the selected width as a 32-bit shift and subtraction whose
resulting bit pattern is zero-extended into the stored 64-bit word.

## Depends on

- [Finite-width implementation model](word-model.md)

## Human transcription review

Check that the comparison and right shift use signed `Py_ssize_t` semantics,
the loop guard matches C exactly, and only the mask expression uses the
selected 32-bit `int` width before widening. In particular, do not silently replace
the mask by a 64-bit shift or by the arbitrary-precision mask in
`listsort.md`.

ISO C does not define every large signed shift exercised by the full modeled
input domain (`1 << 31` is not representable as a positive `int`, and a shift
count at least 32 is outside the type width). The zero-extended `BitVec 32`
operation is therefore the project's selected machine-word convention for
those cases; it is not claimed to be portable C behavior. The downstream
roadmap separates the low-exponent exact-arithmetic bridge from the
unconditional output-band theorem for this reason.

## Sources

- [Verbatim `merge_init`](../../sources/listobject-excerpts.md#merge-init)
- [CPython adaptive-minrun explanation](../../sources/listsort.md#computing-minrun)
