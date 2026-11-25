# Project

Let participants, payload sorts and labels have decidable equality. The projection of a finite global type onto a participant (Def. 4.1, finite fragment) is a partial map to local types. The sender and receiver of a message or choice project it to a send, receive, select or branch; a third party skips the interaction, and on a choice it requires every branch to project to brace-equal local types and takes that common projection (plain merging). An interaction whose sender equals its receiver has no projection.
