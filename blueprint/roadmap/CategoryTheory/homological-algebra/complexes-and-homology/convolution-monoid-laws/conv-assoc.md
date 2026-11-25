# Conv assoc

Graded convolution associativity, up to the `add_assoc` degree transport.

The transport uses only stdlib `cast`/`congrArg`; its computation is the local
`cochain_cast_v` bridge above. After `Cochain.ext`, both sides unfold via
`conv_tensor_v` and the `congr_v` forms of `tensor_conv_factor_left`/
`tensor_conv_factor_right` to the five-fold composites of
`conv_assoc_hmid_middle_v`, which closes the components (outer `tensorHom`
factors are definitionally the `▷`/`◁` whiskerings by the pinned monoidal
structure). No new convolution definition and no stronger hypotheses.
