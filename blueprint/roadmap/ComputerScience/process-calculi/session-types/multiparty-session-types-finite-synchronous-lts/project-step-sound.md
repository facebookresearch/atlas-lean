# Soundness of projection for global steps

Let participants, payload sorts and labels have decidable equality. Soundness of projection for steps: if `G` is a well-formed global type and `G` steps to `G'` by a label, then the sender and receiver of the label are distinct, and for every participant both projections of `G` and `G'` are defined; the sender's projection steps by the sending action to the new projection, the receiver's projection steps by the receiving action, and the projection of every other participant stays brace-equal.
